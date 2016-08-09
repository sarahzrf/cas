{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.Pretty where

import Morte.Core
import Data.Text.Lazy
import Control.Lens hiding (Const)

data DisplayExpr
  = DStar
  | DBox
  | DVar String
  | DLam [(String, DisplayExpr)] DisplayExpr
  | DPi [(String, DisplayExpr)] DisplayExpr
  | Arr DisplayExpr DisplayExpr
  | DApp DisplayExpr DisplayExpr
  | Par DisplayExpr

mapBT :: (a -> b) -> [(t, a)] -> [(t, b)]
mapBT = over (traverse._2)

displayExpr :: Expr X -> DisplayExpr
displayExpr = parenthesize . accumBinders . toDE


toDE :: Expr X -> DisplayExpr
toDE (Const Star)  = DStar
toDE (Const Box)   = DBox
toDE (Var v)       = DVar . unpack . pretty $ v
toDE (Lam v d b)   = DLam [(unpack v, displayExpr d)] (displayExpr b)
toDE (Pi  "_" d c) = Arr             (displayExpr d) (displayExpr c)
toDE (Pi  v d c)   = DPi  [(unpack v, displayExpr d)] (displayExpr c)
toDE (App f a)     = DApp (displayExpr f) (displayExpr a)
toDE (Embed x)     = absurd x


accumBinders :: DisplayExpr -> DisplayExpr
accumBinders (DLam p (DLam p' b)) = accumBinders $ DLam (p ++ p') b
accumBinders (DPi  p (DPi  p' c)) = accumBinders $ DPi  (p ++ p') c
accumBinders (DLam p b) = DLam (mapBT accumBinders p) (accumBinders b)
accumBinders (DPi  p c) = DPi  (mapBT accumBinders p) (accumBinders c)
accumBinders (Arr  d c) = Arr  (accumBinders d) (accumBinders c)
accumBinders (DApp f a) = DApp (accumBinders f) (accumBinders a)
accumBinders (Par e)    = Par  (accumBinders e)
accumBinders e = e


{-
DLam: binds right at 1
DPi:  binds right at 1
Arr:  binds left at 3, binds right at 2
DApp: binds left at 4, binds right at 5
-}

weakRight, weakLeft :: DisplayExpr -> Bool
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

mpar = \case True -> Par; False -> id

parenthesize :: DisplayExpr -> DisplayExpr
parenthesize (DLam p b) = DLam (mapBT parenthesize p) (parenthesize b)
parenthesize (DPi  p c) = DPi  (mapBT parenthesize p) (parenthesize c)
parenthesize (Arr  d c) = Arr (mpar (weakRight d) (parenthesize d)) (parenthesize c)
parenthesize (DApp f a) = DApp (mpar (weakRight f) (parenthesize f)) (mpar (weakLeft a) (parenthesize a))
parenthesize (Par e)    = Par (parenthesize e)
parenthesize e          = e

