{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
module ProofCas.Backends.SFP.Rendering where

import Reflex.Dom
import Utils.Pretty
import Utils.ABT
import Utils.Telescope
import Utils.Vars
import Dependent.Core.Term
import Control.Monad
import Data.Functor.Foldable
import Data.Functor.Compose
import Data.Monoid
import Data.List
import qualified Data.Text as T
import ProofCas.Rendering
import ProofCas.Backends.SFP.Paths

data Term' a = Var' Variable | In' (TermF (Scope' a)) deriving Functor
data Scope' a =
  Scope' {
    names' :: [String],
    freeNames' :: [FreeVar],
    body' :: a
  } deriving Functor

newtype Subterm = Subterm (TPath, Term)
type instance Base Subterm = Compose ((,) TPath) Term'
instance Recursive Subterm where
  project (Subterm (pa, Var v)) = Compose (pa, Var' v)
  project (Subterm (pa, In t)) = Compose (pa, In' t')
    where rescope s (Scope n f b) = Scope' n f (Subterm (s:pa, b))
          rescopeMotive (CaseMotive (BindingTelescope b r)) =
            CaseMotive (BindingTelescope (zipWith (rescope . MotiveArg) [0..] b) (rescope MotiveRet r))
          -- this is incorrect actually :(
          rescopeClause n (Clause p r) =
            Clause (map (fmap (rescope AssertionPatArg)) p) (rescope (ClauseBody n) r)
          t' = case t of
            Defined v  -> Defined v
            Ann t y    -> Ann (rescope AnnTerm t) (rescope AnnType y)
            Type       -> Type
            Fun d c    -> Fun (rescope FunArg d) (rescope FunRet c)
            Lam b      -> Lam (rescope LamBody b)
            App f a    -> App (rescope AppFun f) (rescope AppArg a)
            Con i a    -> Con i (zipWith (rescope . ConArg) [0..] a)
            Case a o c -> Case (zipWith (rescope . CaseArg) [0..] a) (rescopeMotive o) (zipWith rescopeClause [0..] c)


wrapP :: MonadWidget t m => Bool -> m a -> m a
wrapP True  = bracket "(" ")"
wrapP False = id


sfpPrec :: Term' Subterm -> Term' (Subterm, Bool)
sfpPrec = fmap go
  where
    go sub@(Subterm (pa, t))
      | s:_ <- pa = (sub, not (parenLoc t s))
      | otherwise = (sub, False)

sfpCls :: Term' a -> T.Text
sfpCls = \case
  Var' (Free _)     -> "free"
  Var' (Bound _ _)  -> "bound"
  Var' (Meta _)     -> "meta"
  In'  (Defined _)  -> "defined"
  In'  (Ann _ _)    -> "ann"
  In'  Type         -> "type"
  In'  (Fun _ _)    -> "fun"
  In'  (Lam _)      -> "lam"
  In'  (App _ _)    -> "app"
  In'  (Con _ _)    -> "con"
  In'  (Case _ _ _) -> "case"

sfpStep :: MonadWidget t m => Term' (Render t pa m) -> Render t pa m
sfpStep (Var' v) = textSpan . T.pack . name $ v
sfpStep (In' t) = case t of
  Defined v  -> textSpan (T.pack v)
  Ann t y    -> body' t >> textSpan " : " >> body' y
  Type       -> textSpan "Type"
  Fun d c    -> do
    wrapP True $ do
      textSpan $ T.pack (unwords (names' c)) <> " : "
      body' d
    textSpan " \8594 "
    body' c
  Lam b      -> do
    textSpan "\955"
    wrapP False . textSpan . T.pack . unwords . names' $ b
    textSpan " \8594 "
    body' b
  App f a    -> body' f >> textSpan " " >> wrapP False (body' a)
  Con i []   -> textSpan (T.pack i)
  Con i a    -> do
    textSpan $ T.pack i <> " "
    sepBy_ " " a $ wrapP False . body'
  Case a o c -> do
    textSpan "case "
    sepBy_ " || " a body'

    textSpan " motive "
    let CaseMotive (BindingTelescope b r) = o
    forM_ (zip b (names' r)) $ \(b, v) -> do
      textSpan $ "(" <> T.pack v <> " : "
      body' b
      textSpan ") || "
    body' r

    textSpan " of "
    sepBy_ " | " c $ \(Clause p r) -> do
      textSpan $ T.pack . intercalate " || " . map (const "placeholder" :: PatternF (Scope' (Render t pa m)) -> [Char]) $ p
      textSpan " \8594 "
      body' r

    textSpan " end"

