{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
module ProofCas.Backends.SFP.Rendering where

import Utils.Pretty
import Utils.ABT
import Utils.Telescope
import Utils.Vars
import Dependent.Core.Term
import Data.Monoid
import Data.Char
import qualified Data.Text as T
import Data.String
import ProofCas.Rendering
import ProofCas.Rendering.TH
import ProofCas.Backends.SFP.Paths

opFor :: Term -> Maybe String
opFor = \case Var v -> go (name v); In (Defined d) -> go d; _ -> Nothing
  where go ('o':'p':'_':n) | all isDigit n = Just . pure . toEnum . read $ n
        go _ = Nothing
conOpFor :: String -> Maybe String
conOpFor ('O':'p':'_':n) | all isDigit n = Just . pure . toEnum . read $ n
conOpFor _ = Nothing
pattern S b <- Scope{body=b}
pattern BinOp x o y <- App (S (In (App (S (opFor -> Just o)) x))) y
pattern TrinCon x o s y <- Con (conOpFor -> Just o) [s, x, y]


data TermParenLoc' = Normal TermParenLoc | BinOpArg

sfpPrec :: Term -> TermParenLoc' -> Bool
sfpPrec (In (BinOp x o y)) (Normal FunRet) = False
sfpPrec (In (TrinCon x o s y)) (Normal FunRet) = False
sfpPrec (In (BinOp x o y)) _ = True
sfpPrec (In (TrinCon x o s y)) _ = True
sfpPrec t (Normal l) = not (parenLoc t l)
sfpPrec (Var _) BinOpArg = False
sfpPrec (In (Defined _)) BinOpArg = False
sfpPrec (In (App _ _)) BinOpArg = False
sfpPrec t BinOpArg = True


sfpDisplay :: TPath -> Maybe TermParenLoc' -> Term -> DTerm TPath
sfpDisplay cur ml t = DTerm cls cur (maybe False (sfpPrec t) ml) layer
  where (cls, layer) = sfpLayer rec t
        rec pa l t' = sfpDisplay (pa ++ cur) (Just l) (body t')

sfpLayer :: (TPath -> TermParenLoc' -> Scope TermF -> DTerm TPath) -> Term -> (T.Text, RenderLayer (DTerm TPath))
sfpLayer rec (Var v) = let n = name v in (cls, fromString n)
  where cls = case v of Free _ -> "free"; Bound _ _ -> "bound"; Meta _ -> "meta"
sfpLayer rec (In t) = let rec' s = rec [s] (Normal s); irec s = zipWith (rec' . s) [0..] in case t of
  Defined v
    -> ("defined", fromString v)
  Ann (rec' AnnTerm -> t) (rec' AnnType -> y)
    -> ("ann", [rl|%t : %y|])
  Type
    -> ("type", fromString "Type")
  Fun (rec' FunArg -> d) c_@(rec' FunRet -> c)
    -> let a = unwords . names $ c_ in
       ("fun", [rl|($a : %d) → %c|])
  Lam b_@(rec' LamBody -> b)
    -> let a = unwords . names $ b_
    in ("lam", [rl|λ$a → %b|])
  BinOp (rec [AppArg, AppFun] BinOpArg -> x) o (rec [AppArg] BinOpArg -> y)
    -> ("binop", [rl|%x $o %y|])
  App (rec' AppFun -> f) (rec' AppArg -> a)
    -> ("app", [rl|%f %a|])
  Con i []
    -> ("con", fromString i)
  TrinCon (rec [ConArg 1] BinOpArg -> x) o
          (rec [ConArg 0] (Normal LamBody) -> s)
          (rec [ConArg 2] BinOpArg -> y)
    -> ("trinop", [rl|%x $o<sub>%s</sub> %y|])
  Con i (irec ConArg -> a)
    -> ("con", [rl|$i |] <> sepBy " " (map rlrec a))
  Case (irec CaseArg -> a)
       (CaseMotive (BindingTelescope (irec MotiveArg -> b) r_@(rec' MotiveRet -> r)))
       (irec ClauseBody . map (\(Clause _ r) -> r) -> c)
    -> let a'   = sepBy " || " (map rlrec a)
           o'   = sepBy " || " (zipWith (\b v -> [rl|($v : %b)|]) b (names r_))
           body = sepBy " | "  (map (\c -> [rl|placeholder → %c|]) c)
    in ("case", [rl|case ,a' motive ,o' || %r of ,body end|])

