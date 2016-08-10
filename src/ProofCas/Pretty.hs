{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.Pretty where

import Morte.Core hiding (Path)
import Data.Text.Lazy
import ProofCas.Paths

data DELevel a
  = DStar
  | DBox
  | DVar String
  | DLam [(String, a)] a
  | DPi [(String, a)] a
  | Arr a a
  | DApp a a
  deriving Functor
data DisplayExpr' = NoPar' Path (DELevel DisplayExpr')
data DisplayExpr = NoPar Path (DELevel DisplayExpr) | Par Path (DELevel DisplayExpr)

displayExpr :: Expr X -> DisplayExpr
displayExpr = parenthesize . accumBinders . toDE' []


toDE' :: Path -> Expr X -> DisplayExpr'
toDE' cur e = NoPar' cur (go e)
  where
    go (Const Star) = DStar
    go (Const Box)  = DBox
    go (Var v)      = DVar . unpack . pretty $ v
    go (Lam v d b)  = DLam [(unpack v, toDE' (LamDom:cur) d)] (toDE' (LamBody:cur) b)
    go (Pi "_" d c) = Arr (toDE' (PiDom:cur) d) (toDE' (PiCod:cur) c)
    go (Pi v d c)   = DPi [(unpack v, toDE' (PiDom:cur) d)] (toDE' (PiCod:cur) c)
    go (App f a)    = DApp (toDE' (AppFunc:cur) f) (toDE' (AppArg:cur) a)
    go (Embed x)    = absurd x


accumBinders :: DisplayExpr' -> DisplayExpr'
accumBinders (NoPar' pa e) = NoPar' pa (go e)
  where
    go (DLam p (NoPar' _ (DLam p' b))) = go $ DLam (p ++ p') b
    go (DPi  p (NoPar' _ (DPi  p' b))) = go $ DPi  (p ++ p') b
    go e = fmap accumBinders e


{-
DLam: binds right at 1
DPi:  binds right at 1
Arr:  binds left at 3, binds right at 2
DApp: binds left at 4, binds right at 5
-}

weakRight, weakLeft :: DELevel a -> Bool
weakRight = \case
  (DLam _ _) -> True
  (DPi  _ _) -> True
  (Arr  _ _) -> True
  _ -> False
weakLeft = \case
  (DLam _ _) -> True
  (DPi  _ _) -> True
  (Arr  _ _) -> True
  (DApp _ _)   -> True
  _ -> False

mpar = \case True -> Par; False -> NoPar

parenthesize :: DisplayExpr' -> DisplayExpr
parenthesize (NoPar' pa e) = NoPar pa (go e)
  where
    go :: DELevel DisplayExpr' -> DELevel DisplayExpr
    go (Arr  (NoPar' pa d) (NoPar' pa' c)) = Arr (mpar (weakRight d) pa (go d)) (NoPar pa' (go c))
    go (DApp (NoPar' pa f) (NoPar' pa' a)) = DApp (mpar (weakRight f) pa (go f)) (mpar (weakLeft a) pa' (go a))
    go e = fmap parenthesize e

