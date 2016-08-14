{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.Pretty where

import Morte.Core hiding (Path)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import ProofCas.Paths

data DELevel a
  = DStar
  | DBox
  | DVar T.Text
  | DLam {isFirst :: Bool, isLast :: Bool, varName :: T.Text, dom :: a, bod :: a}
  | DPi  {isFirst :: Bool, isLast :: Bool, varName :: T.Text, dom :: a, cod :: a}
  | Arr a a
  | DApp a a
  deriving Functor
data DisplayExpr' = NoPar' Path (DELevel DisplayExpr')
data DisplayExpr = NoPar Path (DELevel DisplayExpr) | Par Path (DELevel DisplayExpr)

displayExpr :: Expr X -> DisplayExpr
displayExpr = parenthesize . markBinders . toDE' []


toDE' :: Path -> Expr X -> DisplayExpr'
toDE' cur e = NoPar' cur (go e)
  where
    go (Const Star) = DStar
    go (Const Box)  = DBox
    go (Var v)      = DVar . T.pack . TL.unpack . pretty $ v
    go (Lam v d b)  = DLam True True (T.pack (TL.unpack v)) (toDE' (LamDom:cur) d) (toDE' (LamBody:cur) b)
    go (Pi "_" d c) = Arr (toDE' (PiDom:cur) d) (toDE' (PiCod:cur) c)
    go (Pi v d c)   = DPi True True (T.pack (TL.unpack v)) (toDE' (PiDom:cur) d) (toDE' (PiCod:cur) c)
    go (App f a)    = DApp (toDE' (AppFunc:cur) f) (toDE' (AppArg:cur) a)
    go (Embed x)    = absurd x


markBinders :: DisplayExpr' -> DisplayExpr'
markBinders (NoPar' pa e) = NoPar' pa (go e)
  where
    go (la@DLam{bod=NoPar' pa (la'@DLam{})}) = la{isLast=False, bod=NoPar' pa (go la'{isFirst=False})}
    go (pi@DPi {cod=NoPar' pa (pi'@DPi {})}) = pi{isLast=False, cod=NoPar' pa (go pi'{isFirst=False})}
    go e = fmap markBinders e


{-
DLam: binds right at 1
DPi:  binds right at 1
Arr:  binds left at 3, binds right at 2
DApp: binds left at 4, binds right at 5
-}

weakRight, weakLeft :: DELevel a -> Bool
weakRight = \case
  (DLam _ _ _ _ _) -> True
  (DPi  _ _ _ _ _) -> True
  (Arr  _ _) -> True
  _ -> False
weakLeft = \case
  (DLam _ _ _ _ _) -> True
  (DPi  _ _ _ _ _) -> True
  (Arr  _ _) -> True
  (DApp _ _) -> True
  _ -> False

mpar = \case True -> Par; False -> NoPar

parenthesize :: DisplayExpr' -> DisplayExpr
parenthesize (NoPar' pa e) = NoPar pa (go e)
  where
    go :: DELevel DisplayExpr' -> DELevel DisplayExpr
    go (Arr  (NoPar' pa d) (NoPar' pa' c)) = Arr (mpar (weakRight d) pa (go d)) (NoPar pa' (go c))
    go (DApp (NoPar' pa f) (NoPar' pa' a)) = DApp (mpar (weakRight f) pa (go f)) (mpar (weakLeft a) pa' (go a))
    go e = fmap parenthesize e

