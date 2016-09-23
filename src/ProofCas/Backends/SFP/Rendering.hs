{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.Backends.SFP.Rendering where

import Reflex.Dom
import Utils.Pretty
import Utils.ABT
import Utils.Telescope
import Utils.Vars
import Dependent.Core.Term
import Control.Monad
import Control.Monad.Reader
import Data.Functor.Compose
import Data.Monoid
import Data.Char
import Data.List
import qualified Data.Text as T
import ProofCas.Rendering
import ProofCas.Backends.SFP.Paths

data TermParenLoc' = Normal TermParenLoc | BinOpArg

wrapP :: MonadWidget t m => m a -> m a
wrapP = bracket "(" ")"


data PathABT f
  = PathVar TPath Variable
  | PathIn TPath (f (PathScope f))
data PathScope f =
  PathScope {
    pathNames :: [String],
    pathFreeNames :: [FreeVar],
    pathBody :: PathABT f
  }
type PathTerm = PathABT TermF
addPaths :: Term -> PathTerm
addPaths = go []
  where go cur (Var v) = PathVar cur v
        go cur (In t) = PathIn cur $ case t of
          Defined v  -> Defined v
          Ann t y    -> Ann (t@:AnnTerm) (y@:AnnType)
          Type       -> Type
          Fun d c    -> Fun (d@:FunArg) (c@:FunRet)
          Lam b      -> Lam (b@:LamBody)
          App f a    -> App (f@:AppFun) (a@:AppArg)
          Con i a    -> Con i (zipWith (\n a -> a@:ConArg n) [0..] a)
          Case a o c -> Case (zipWith (\n a -> a@:CaseArg n) [0..] a) (motive o) (zipWith clause [0..] c)
          where Scope n f b@:s = PathScope n f (go (s:cur) b)
                motive (CaseMotive (BindingTelescope b r)) =
                  CaseMotive (BindingTelescope (zipWith (\n a -> a@:MotiveArg n) [0..] b) (r@:MotiveRet))
                -- this is incorrect actually :(
                clause n (Clause p r) =
                  Clause (map (fmap (@:AssertionPatArg)) p) (r@:ClauseBody n)

unPath :: PathTerm -> Term
unPath (PathVar _ v) = Var v
unPath (PathIn  _ t) = In (fmap unPathScope t)
  where unPathScope (PathScope n f b) = Scope n f (unPath b)


opFor :: PathTerm -> Maybe T.Text
opFor = \case PathVar _ v -> go (name v); PathIn _ (Defined d) -> go d; _ -> Nothing
  where go ('o':'p':'_':n) | all isDigit n = Just . T.singleton . toEnum . read $ n
        go _ = Nothing
conOpFor :: String -> Maybe T.Text
conOpFor ('O':'p':'_':n) | all isDigit n = Just . T.singleton . toEnum . read $ n
conOpFor _ = Nothing
pattern I b <- PathIn _ b
pattern S b <- PathScope{pathBody=b}
pattern BinOp x o y <- App (S (PathIn _ (App (S (opFor -> Just o)) x))) y
pattern TrinCon x o s y <- Con (conOpFor -> Just o) [s, x, y]

sfpPrec :: PathTerm -> TermParenLoc' -> Bool
sfpPrec (I (BinOp x o y)) (Normal FunRet) = True
sfpPrec (I (TrinCon x o s y)) (Normal FunRet) = True
sfpPrec (I (BinOp x o y)) _ = False
sfpPrec (I (TrinCon x o s y)) _ = False
sfpPrec t (Normal l) = parenLoc (unPath t) l
sfpPrec (PathVar _ _) BinOpArg = True
sfpPrec (I (Defined _)) BinOpArg = True
sfpPrec (I (App _ _)) BinOpArg = True
sfpPrec t BinOpArg = False

sfpStep :: StepFunc TermParenLoc' TPath PathTerm
sfpStep (PathVar pa v) = (cls v, pa, const . textSpan . T.pack . name $ v)
  where cls = \case Free _ -> "free"; Bound _ _ -> "bound"; Meta _ -> "meta"
sfpStep (PathIn pa t) = (\(y, b) -> (y, pa, runReaderT b)) $ case t of
  Defined v   -> ("defined", textSpan (T.pack v))
  Ann t y     -> ("ann", rec' AnnTerm t >> textSpan " : " >> rec' AnnType y)
  Type        -> ("type", textSpan "Type")
  Fun d c     -> ("fun", do
    wrapP $ do
      textSpan $ T.pack (unwords (pathNames c)) <> " : "
      rec' FunArg d
    textSpan " \8594 "
    rec' FunRet c)
  Lam b       -> ("lam", do
    textSpan "\955"
    textSpan . T.pack . unwords . pathNames $ b
    textSpan " \8594 "
    rec' LamBody b)
  BinOp x o y -> ("binop", ReaderT $ \rec -> do
    rec BinOpArg (pathBody x)
    textSpan (" " <> o <> " ")
    rec BinOpArg (pathBody y))
  App f a     -> ("app", rec' AppFun f >> textSpan " " >> rec' AppArg a)
  Con i []    -> ("con", textSpan (T.pack i))
  TrinCon x o s y -> ("trinop", ReaderT $ \rec -> do
    rec BinOpArg (pathBody x)
    textSpan (" " <> o)
    el "sub" $ rec (Normal FunRet) (pathBody s)
    textSpan " "
    rec BinOpArg (pathBody y))
  Con i a     -> ("con", do
    textSpan $ T.pack i <> " "
    sepBy_ " " (zip [0..] a) (uncurry (rec' . ConArg)))
  Case a o c  -> ("case", do
    textSpan "case "
    sepBy_ " || " (zip [0..] a) (uncurry (rec' . CaseArg))

    textSpan " motive "
    let CaseMotive (BindingTelescope b r) = o
    forM_ (zip3 [0..] b (pathNames r)) $ \(n, b, v) -> do
      textSpan $ "(" <> T.pack v <> " : "
      rec' (MotiveArg n) b
      textSpan ") || "
    rec' MotiveRet r

    textSpan " of "
    sepBy_ " | " (zip [0..] c) $ \(n, Clause p r) -> do
      textSpan $ T.pack . intercalate " || " . map (const "placeholder") $ p
      textSpan " \8594 "
      rec' (ClauseBody n) r

    textSpan " end")
  where rec' l t = ReaderT $ \rec -> rec (Normal l) (pathBody t)

