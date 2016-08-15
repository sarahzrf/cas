{-# LANGUAGE TemplateHaskell #-}
module ProofCas.Proofs where

import Morte.Core
import Control.Lens hiding (Context)

data Status =
  Status {
    _statusCtx     :: Context (Expr X),
    _statusTheorem :: Expr X,
    _statusProof   :: Expr X
  }

makeLenses ''Status

