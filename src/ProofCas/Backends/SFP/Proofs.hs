{-# LANGUAGE PatternSynonyms #-}
module ProofCas.Backends.SFP.Proofs where

import Utils.ABT
import Utils.Vars
import Dependent.Core.Term
import Control.Lens hiding (rewrite)
import Control.Monad
import Data.Maybe
import ProofCas.Rendering (StPart(..))
import ProofCas.Backends.SFP.Status
import ProofCas.Backends.SFP.Paths

proofStep :: (Status -> Either String Status) -> Status -> Either String Status
proofStep f st = do st' <- f st; checkStatus st'; return st'


evalAt :: StPath -> Status -> Either String Status
evalAt sel st = st & stpath sel (evalIn st)

boundIn :: Term -> [String]
boundIn (Var _) = []
boundIn (In  t) = foldMap (\sc -> names sc ++ boundIn (body sc)) t

definedNames :: Term -> [String]
definedNames (Var _)          = []
definedNames (In (Defined v)) = [v]
definedNames (In t)           = foldMap (definedNames . body) t

freshFor :: Term -> String
freshFor t = freshenName unusable "x"
  where unusable = boundIn t ++ freeVarNames t ++ definedNames t

factorOut :: TPath -> Term -> Maybe Term
factorOut pa t = do
  a <- t^?tpath pa
  let noBound (Var (Bound _ _)) = False
      noBound (Var _) = True
      noBound (In t)  = all (noBound . body) t
  guard (noBound a)
  let param    = freshFor t
      body     = t & tpath pa.~Var (Free (FreeVar param))
  return $ appH (lamH param body) a

factorOutSt :: StPath -> Status -> Either String Status
factorOutSt (stpa, pa) = maybe (Left msg) Right . stpart stpa (factorOut pa)
  where msg = "Can't factor out - contains bound variable"


handleDrop :: StPath -> StPath -> Status -> Either String Status
handleDrop (Assm v, [ConArg 2]) (Thm, pa) = rewriteLtr v pa
handleDrop (Assm v, [ConArg 1]) (Thm, pa) = rewriteRtl v pa
handleDrop _ _ = Right

pattern S t <- Scope _ _ t
pattern App' f x <- In (App (Scope _ _ f) (Scope _ _ x))

rewriteLtr :: String -> TPath -> Status -> Either String Status
rewriteLtr v pa st = maybe (Left "couldn't rewrite") Right $ do
  In (Con "Eq" [S ty, S lhs, S rhs]) <- st^?stpath (Assm v, [])
  let Status{_statusTheorem=oldThm, _statusProof=oldPrf} = st
  App' p _ <- factorOut pa oldThm
  let newPrf = foldl1 appH [In (Defined "eq_elim"), ty, p, lhs, rhs, Var (Free (FreeVar v)), oldPrf]
  return $ st & stpath (Thm, pa).~rhs & (stpart Prf).~newPrf

rewriteRtl :: String -> TPath -> Status -> Either String Status
rewriteRtl v pa st = maybe (Left "couldn't rewrite") Right $ do
  In (Con "Eq" [S ty, S lhs, S rhs]) <- st^?stpath (Assm v, [])
  let Status{_statusTheorem=oldThm, _statusProof=oldPrf} = st
      sym = foldl1 appH [In (Defined "eq_sym"), ty, lhs, rhs, Var (Free (FreeVar v))]
  App' p _ <- factorOut pa oldThm
  let newPrf = foldl1 appH [In (Defined "eq_elim"), ty, p, rhs, lhs, sym, oldPrf]
  return $ st & stpath (Thm, pa).~lhs & (stpart Prf).~newPrf

