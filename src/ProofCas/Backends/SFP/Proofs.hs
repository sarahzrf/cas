{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
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
import Data.Foldable hiding (fold)
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
      body     = t & tpath pa.~F param
  return $ appH (lamH param body) a

factorOutSt :: StPath -> Status -> Either String Status
factorOutSt (stpa, pa) = maybe (Left msg) Right . stpart stpa (factorOut pa)
  where msg = "Can't factor out - contains bound variable"


pattern M n = Var (Meta (MetaVar n))
pattern F n = Var (Free (FreeVar n))
pattern S t <- Scope _ _ t
pattern App' f x <- In (App (Scope _ _ f) (Scope _ _ x))

handleDrop :: StPath -> StPath -> Status -> Either String Status
handleDrop stpa stpa' st = fromMaybe (Right st) $ alaf First foldMap (\f -> f stpa stpa' st) handlers
  where handlers = [rewrite]

useAs :: Term -> Term -> Term -> Status -> Either String (Term, Term, Substitution TermF)
useAs ty prf goal st = do
  let Status sig defs ctx _ _ = st
      unify' s t = runElaborator (unify substitution context s t) sig defs ctx
      unifyA n t = case (unify' t goal, metaify n t) of (Left _, Just t') -> unifyA (n + 1) t'; (r, _) -> ((,) n) <$> r
      metaify n (In (Fun _ s)) = Just (instantiate s [Var (Meta (MetaVar n))])
      metaify _ _ = Nothing
      meta0 = 1 + fold (\case Meta (MetaVar n) -> n; _ -> 0) (foldl' max 0) (flip const) goal
  (argCount, ((), es)) <- unifyA meta0 ty
  let argsm = mapM (\i -> lookup (MetaVar i) (_substitution es)) [meta0..argCount - 1]
  args <- maybe (Left "Couldn't infer all args") Right argsm
  let ty' = foldl (\(In (Fun _ s)) a -> instantiate s [a]) ty args
      prf' = foldl appH prf args
  return (ty', prf', _substitution es)

rewrite :: StPath -> StPath -> Status -> Maybe (Either String Status)
rewrite stpa@(Assm v, pa@(ConArg n:steps)) stpa'@(Thm, pa') st = do
  guard $ all (==FunRet) steps && n `elem` [1, 2]
  In (Con "Eq" [_, _, _]) <- st^?stpath (parent stpa)
  eqTy <- st^?stpart (Assm v)
  target <- st^?stpath stpa'
  return $ do
    let Status _ _ _ thm prf = st
    App' p _ <- maybe (Left "Rewrite target contains bound variable") Right $ factorOut pa' thm
    let goal = conH "Eq" (if n == 1 then [M 0, M 1, target] else [M 0, target, M 1])
    (In (Con _ [S argTy, S lhs, S rhs]), eqPrf, es) <- useAs eqTy (F v) goal st
    let (from, to, eqPrf') = if n == 1
          then let sym = foldl1 appH [In (Defined "eq_sym"), argTy, lhs, rhs, eqPrf]
               in (rhs, lhs, sym)
          else (lhs, rhs, eqPrf)
        prf' = foldl1 appH [In (Defined "eq_elim"), argTy, p, from, to, eqPrf', prf]
    return $ st & stpath (Thm, pa').~to & (stpart Prf).~prf'
rewrite _ _ _ = Nothing

