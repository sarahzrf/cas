{-# LANGUAGE TemplateHaskell #-}
module ProofCas.Paths where

import Morte.Core hiding (Path)
import Control.Lens
import Control.Monad.State
import qualified Data.Text.Lazy as TL
import Data.List
import Data.Maybe
import ProofCas.Proofs
import ProofCas.Contexts

data EPathStep =
  LamDom | LamBody | PiDom | PiCod | AppFunc | AppArg
  deriving (Eq, Ord, Show)

type EPath = [EPathStep]

data StPart =
  Assm TL.Text Int | Thm | Prf
  deriving (Eq, Ord, Show)

data StPath =
  StPath {
    _statusPart :: StPart,
    _epathPart  :: EPath
  } deriving (Eq, Ord, Show)

makeLenses ''StPath


parent :: EPath -> EPath
parent [] = []
parent (s:ss) = ss

ancestor :: EPath -> EPath -> Bool
ancestor = isSuffixOf


estep :: Applicative f => EPathStep ->
  (Expr a -> f (Expr a)) -> Expr a -> f (Expr a)
estep LamDom  m (Lam v d b) = (\d -> Lam v d b) <$> m d
estep LamBody m (Lam v d b) = (\b -> Lam v d b) <$> m b
estep PiDom   m (Pi  v d c) = (\d -> Pi  v d c) <$> m d
estep PiCod   m (Pi  v d c) = (\c -> Pi  v d c) <$> m c
estep AppFunc m (App f a)   = (\f -> App f a)   <$> m f
estep AppArg  m (App f a)   = (\a -> App f a)   <$> m a
estep _ _ e = pure e

epath ::
  Applicative f => EPath ->
  (Expr a -> f (Expr a)) -> Expr a -> f (Expr a)
epath = foldl' (.) id . reverse . map estep


stpart ::
  Applicative f => StPart ->
  (Expr X -> f (Expr X)) -> Status -> f Status
stpart (Assm v occ) = statusCtx.numbered.aIx (v, occ)
stpart Thm =          statusTheorem
stpart Prf =          statusProof

stpath ::
  Applicative f => StPath ->
  (Expr X -> f (Expr X)) -> Status -> f Status
stpath (StPath stP epaP) = stpart stP.epath epaP


-- not actually very useful - just for interface demo purposes!
swap :: StPath -> StPath -> Status -> Status
swap stpa stpa' = ap fromMaybe $ execStateT $ do
  guard $ not (_epathPart stpa  `ancestor` _epathPart stpa' ||
               _epathPart stpa' `ancestor` _epathPart stpa)
  a <- preuse (stpath stpa)  >>= lift
  b <- preuse (stpath stpa') >>= lift
  stpath stpa  .= b
  stpath stpa' .= a

