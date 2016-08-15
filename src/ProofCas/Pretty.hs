{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module ProofCas.Pretty where

import Morte.Core
import Control.Lens hiding (Context, Const)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Data.Bool
import ProofCas.Contexts
import ProofCas.Paths
import ProofCas.Proofs

data DELevel a
  = DStar
  | DBox
  | DVar T.Text
  | DLam {isFirst :: Bool, isLast :: Bool, varName :: T.Text, dom :: a, bod :: a}
  | DPi  {isFirst :: Bool, isLast :: Bool, varName :: T.Text, dom :: a, cod :: a}
  | Arr a a
  | DApp a a
  deriving Functor
data DisplayExpr' = NoPar' StPath (DELevel DisplayExpr')
data DisplayExpr = NoPar StPath (DELevel DisplayExpr) | Par StPath (DELevel DisplayExpr)

data DisplayStatus =
  DisplayStatus {
    _dstatusCtx     :: Context DisplayExpr,
    _dstatusTheorem :: DisplayExpr,
    _dstatusProof   :: DisplayExpr
  }

makeLenses ''DisplayStatus


displayStatus :: Status -> DisplayStatus
displayStatus (Status ctx thm prf) =
  DisplayStatus (displayCtx ctx) (displayExpr Thm thm) (displayExpr Prf prf)

displayCtx :: Context (Expr X) -> Context DisplayExpr
displayCtx = numbered.traverse%~disp
  where disp ((v, occ), e) = ((v, occ), displayExpr (Assm v occ) e)


displayExpr :: StPart -> Expr X -> DisplayExpr
displayExpr sp = parenthesize . markBinders . toDE' sp []

toDE' :: StPart -> EPath -> Expr X -> DisplayExpr'
toDE' sp cur e = NoPar' (StPath sp cur) $ case e of
  Const Star -> DStar
  Const Box  -> DBox
  Var v      -> DVar . TL.toStrict . pretty $ v
  Lam v d b  -> DLam True True (TL.toStrict v) (toDE' sp (LamDom:cur) d) (toDE' sp (LamBody:cur) b)
  Pi "_" d c -> Arr (toDE' sp (PiDom:cur) d) (toDE' sp (PiCod:cur) c)
  Pi v d c   -> DPi True True (TL.toStrict v) (toDE' sp (PiDom:cur) d) (toDE' sp (PiCod:cur) c)
  App f a    -> DApp (toDE' sp (AppFunc:cur) f) (toDE' sp (AppArg:cur) a)
  Embed x    -> absurd x

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
  DStar    -> False
  DBox     -> False
  DVar _   -> False
  DApp _ _ -> False
  _ -> True
weakLeft = \case
  DStar  -> False
  DBox   -> False
  DVar _ -> False
  _ -> True
parenthesize :: DisplayExpr' -> DisplayExpr
parenthesize (NoPar' pa e) = NoPar pa (go e)
  where
    mpar = bool NoPar Par
    go :: DELevel DisplayExpr' -> DELevel DisplayExpr
    go (Arr  (NoPar' pa d) (NoPar' pa' c)) = Arr (mpar (weakRight d) pa (go d)) (NoPar pa' (go c))
    go (DApp (NoPar' pa f) (NoPar' pa' a)) = DApp (mpar (weakRight f) pa (go f)) (mpar (weakLeft a) pa' (go a))
    go e = fmap parenthesize e

