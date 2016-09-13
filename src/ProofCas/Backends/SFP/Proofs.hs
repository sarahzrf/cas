{-# LANGUAGE PatternSynonyms #-}
module ProofCas.Backends.SFP.Proofs where

import Utils.ABT
import Utils.Vars
import Utils.Unifier
import Dependent.Core.Term
import Dependent.Unification.Unification
import Dependent.Unification.Elaborator
import Control.Lens hiding (rewrite)
import Control.Monad
import Data.Maybe
import Data.Monoid
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


pattern S t <- Scope _ _ t
pattern App' f x <- In (App (Scope _ _ f) (Scope _ _ x))

handleDrop :: StPath -> StPath -> Status -> Either String Status
handleDrop stpa stpa' st = fromMaybe (Right st) $ alaf First foldMap (\f -> f stpa stpa' st) handlers
  where handlers = [rewrite]

rewrite :: StPath -> StPath -> Status -> Maybe (Either String Status)
rewrite stpa@(Assm v, pa@(ConArg n:steps)) stpa'@(Thm, pa') st = do
  guard $ all (==FunRet) steps && n `elem` [1, 2]
  In (Con "Eq" [_, _, _]) <- st^?stpath (parent stpa)
  eqTy <- st^?stpart (Assm v)
  target <- st^?stpath stpa'
  return $ do
    let Status sig defs ctx thm prf = st
    App' p _ <- maybe (Left "Rewrite target contains bound variable") Right $ factorOut pa' thm
    let metaify n (In (Fun _ s)) = metaify (n + 1) (instantiate s [Var (Meta (MetaVar n))])
        metaify n t = (n, t)
        (argCount, metaified) = metaify 0 eqTy
        In (Con _ [_, S lhsMeta, S rhsMeta]) = metaified
        fromMeta = if n == 1 then rhsMeta else lhsMeta
    ((), es) <- runElaborator (unify substitution context fromMeta target) sig defs ctx
    let argsm = mapM (\i -> lookup (MetaVar i) (_substitution es)) [0..argCount - 1]
    args <- maybe (Left "Couldn't infer all args to hypothesis") Right argsm
    let eqTy' = foldl (\(In (Fun _ s)) a -> instantiate s [a]) eqTy args
        In (Con _ [S argTy, S lhs, S rhs]) = eqTy'
        eqPrf = foldl appH (Var (Free (FreeVar v))) args
        (from, to, eqPrf') = if n == 1
          then let sym = foldl1 appH [In (Defined "eq_sym"), argTy, lhs, rhs, eqPrf]
               in (rhs, lhs, sym)
          else (lhs, rhs, eqPrf)
        prf' = foldl1 appH [In (Defined "eq_elim"), argTy, p, from, to, eqPrf', prf]
    return $ st & stpath (Thm, pa').~to & (stpart Prf).~prf'
rewrite _ _ _ = Nothing

