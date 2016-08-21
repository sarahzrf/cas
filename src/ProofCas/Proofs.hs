module ProofCas.Proofs where

import Utils.ABT
import Utils.Vars
import Utils.Plicity
import DependentImplicit.Core.Term
import DependentImplicit.Unification.Elaborator
import Control.Lens
import Control.Monad
import Data.Maybe
import ProofCas.Status
import ProofCas.Paths
import Debug.Trace

boundIn :: Term -> [String]
boundIn (Var _) = []
boundIn (In  t) = foldMap (\sc -> names sc ++ boundIn (body sc)) t

definedNames :: Term -> [String]
definedNames (Var _)          = []
definedNames (In (Defined v)) = [v]
definedNames (In t)           = foldMap (definedNames . body) t

factorOut :: TPath -> Term -> Maybe Term
factorOut pa t = do
  a <- t^?tpath pa
  let noBound (Var (Bound _ _)) = False
      noBound (Var _) = True
      noBound (In t)  = all (noBound . body) t
  guard (noBound a)
  let unusable = boundIn t ++ freeVarNames t ++ definedNames t
      param    = freshenName (traceShowId unusable) "x"
      body     = t & tpath pa.~Var (Free (FreeVar param))
  return $ appH Expl (lamH Expl param body) a

factorOutSt :: StPath -> Status -> Status
factorOutSt (StPath stpa pa) = fromMaybe <*> stpart stpa (factorOut pa)

