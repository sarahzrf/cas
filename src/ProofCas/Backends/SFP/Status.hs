{-# LANGUAGE TemplateHaskell #-}
module ProofCas.Backends.SFP.Status where

import Utils.Eval
import DependentImplicit.Core.Term
import DependentImplicit.Unification.Elaborator
import DependentImplicit.Core.Evaluation
import Control.Lens hiding (Context)
import Control.Monad.Reader

data Status =
  Status {
    _statusSignature   :: Signature,
    _statusDefinitions :: Definitions,
    _statusContext     :: Context,
    _statusTheorem     :: Term,
    _statusProof       :: Term
  }

makeLenses ''Status

evalIn :: Status -> Term -> Either String Term
evalIn st t = runReaderT (eval t) env
  where env = definitionsToEnvironment (_statusDefinitions st)

