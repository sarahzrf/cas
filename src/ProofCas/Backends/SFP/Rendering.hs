{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
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
import Data.Monoid
import Data.Char
import Data.List
import qualified Data.Text as T
import ProofCas.Rendering
import ProofCas.Backends.SFP.Paths

data TermParenLoc' = Normal TermParenLoc | BinOpArg

wrapP :: MonadWidget t m => Bool -> m a -> m a
wrapP True  = bracket "(" ")"
wrapP False = id


opFor :: Term -> Maybe T.Text
opFor = \case Var v -> go (name v); In (Defined d) -> go d; _ -> Nothing
  where go ('o':'p':'_':n) | all isDigit n = Just . T.singleton . toEnum . read $ n
        go _ = Nothing
conOpFor :: String -> Maybe T.Text
conOpFor ('O':'p':'_':n) | all isDigit n = Just . T.singleton . toEnum . read $ n
conOpFor _ = Nothing
pattern BinOp x o y <- App Scope{body=In (App Scope{body=(opFor -> Just o)} x)} y
pattern TrinCon x o s y <- Con (conOpFor -> Just o) [s, x, y]

sfpPrec :: Term -> TermParenLoc' -> Bool
sfpPrec (In (BinOp x o y)) (Normal FunRet) = True
sfpPrec (In (TrinCon x o s y)) (Normal FunRet) = True
sfpPrec (In (BinOp x o y)) _ = False
sfpPrec (In (TrinCon x o s y)) _ = False
sfpPrec t (Normal l) = parenLoc t l
sfpPrec (Var _) BinOpArg = True
sfpPrec (In (Defined _)) BinOpArg = True
sfpPrec (In (App _ _)) BinOpArg = True
sfpPrec t BinOpArg = False

sfpStep ::
  MonadWidget t m =>
  ((TermParenLoc' -> TPath -> Term -> Render t TPath m) ->
  Term -> (T.Text, Render t TPath m))
sfpStep rec (Var v) = (cls v, textSpan . T.pack . name $ v)
  where cls = \case Free _ -> "free"; Bound _ _ -> "bound"; Meta _ -> "meta"
sfpStep rec (In t) = case t of
  Defined v   -> ("defined", textSpan (T.pack v))
  Ann t y     -> ("ann", rec' AnnTerm t >> textSpan " : " >> rec' AnnType y)
  Type        -> ("type", textSpan "Type")
  Fun d c     -> ("fun", do
    wrapP True $ do
      textSpan $ T.pack (unwords (names c)) <> " : "
      rec' FunArg d
    textSpan " \8594 "
    rec' FunRet c)
  Lam b       -> ("lam", do
    textSpan "\955"
    wrapP False . textSpan . T.pack . unwords . names $ b
    textSpan " \8594 "
    rec' LamBody b)
  BinOp x o y -> ("binop", do
    rec BinOpArg [AppArg, AppFun] (body x)
    textSpan (" " <> o <> " ")
    rec BinOpArg [AppArg] (body y))
  App f a     -> ("app", rec' AppFun f >> textSpan " " >> rec' AppArg a)
  Con i []    -> ("con", textSpan (T.pack i))
  TrinCon x o s y -> ("trinop", do
    rec BinOpArg [ConArg 1] (body x)
    textSpan (" " <> o)
    el "sub" $ rec (Normal FunRet) [ConArg 0] (body s)
    textSpan " "
    rec BinOpArg [ConArg 2] (body y))
  Con i a     -> ("con", do
    textSpan $ T.pack i <> " "
    sepBy_ " " (zip [0..] a) (uncurry (rec' . ConArg)))
  Case a o c  -> ("case", do
    textSpan "case "
    sepBy_ " || " (zip [0..] a) (uncurry (rec' . CaseArg))

    textSpan " motive "
    let CaseMotive (BindingTelescope b r) = o
    forM_ (zip3 [0..] b (names r)) $ \(n, b, v) -> do
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
  where rec' l t = rec (Normal l) [l] (body t)

