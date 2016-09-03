module ProofCas.Backends.SFP.Proofs where

import Utils.ABT
import Utils.Vars
import Dependent.Core.Term
import Control.Lens
import Control.Monad
import Data.Maybe
import ProofCas.Backends.SFP.Status
import ProofCas.Backends.SFP.Paths

evalAt :: StPath -> Status -> Status
evalAt sel st = either (const st) id $ st & stpath sel (evalIn st)

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
      param    = freshenName unusable "x"
      body     = t & tpath pa.~Var (Free (FreeVar param))
  return $ appH (lamH param body) a

factorOutSt :: StPath -> Status -> Status
factorOutSt (stpa, pa) = fromMaybe <*> stpart stpa (factorOut pa)

