module ProofCas.Backends.SFP.Paths where

import Dependent.Core.Term
import Utils.ABT
import Utils.Vars
import Utils.Telescope
import Control.Lens
import Control.Monad.State
import Data.List
import Data.Maybe
import ProofCas.Rendering
import ProofCas.Backends.SFP.Status

type TPathStep = TermParenLoc

type TPath = [TPathStep]

type StPath = (StPart, TPath)


aIx :: (Eq k, Applicative f) => k -> (a -> f a) -> [(k, a)] -> f [(k, a)]
aIx k m [] = pure []
aIx k m ((k', a):kas)
  | k == k' = (\a' -> (k', a'):kas) <$> m a
  | otherwise = ((k', a):) <$> aIx k m kas


parent :: TPath -> TPath
parent [] = []
parent (s:ss) = ss

ancestor :: TPath -> TPath -> Bool
ancestor = isSuffixOf


-- christ this is ugly
tstep' :: Applicative f => TPathStep ->
  (Scope TermF -> f (Scope TermF)) ->
  TermF (Scope TermF) -> f (TermF (Scope TermF))
tstep' s m t = case (s, t) of
  (AnnTerm,      Ann  t y)   -> (\t -> Ann  t y)   <$> m t
  (AnnType,      Ann  t y)   -> (\y -> Ann  t y)   <$> m y
  (FunArg,       Fun  d c)   -> (\d -> Fun  d c)   <$> m d
  (FunRet,       Fun  d c)   -> (\c -> Fun  d c)   <$> m c
  (LamBody,      Lam  b)     -> (\b -> Lam  b)     <$> m b
  (AppFun,       App  f a)   -> (\f -> App  f a)   <$> m f
  (AppArg,       App  f a)   -> (\a -> App  f a)   <$> m a
  (ConArg n,     Con  i a)   -> (\a -> Con  i a)   <$> ix n m a
  (CaseArg n,    Case a o c) -> (\a -> Case a o c) <$> ix n m a
  (MotiveArg n,  Case a o c) -> (\o -> Case a o c) <$> args (ix n m) o
  (MotiveRet,    Case a o c) -> (\o -> Case a o c) <$> ret m o
  (ClauseBody n, Case a o c) -> (\c -> Case a o c) <$> ix n (body m) c

  (AssertionPatArg, _) ->
    error "TODO"
  (_, _) -> pure t
  where args m (CaseMotive (BindingTelescope a r)) = (\a -> CaseMotive (BindingTelescope a r)) <$> m a
        ret m (CaseMotive (BindingTelescope a r)) = (\r -> CaseMotive (BindingTelescope a r)) <$> m r
        body m (Clause p b) = (\b -> Clause p b) <$> m b

tstep :: Applicative f => TPathStep ->
  (Term -> f Term) -> Term -> f Term
tstep s m (Var v) = pure (Var v)
tstep s m (In t) = In <$> tstep' s m' t
  where m' c@Scope{body=t} = (\t -> c{body=t}) <$> m t

tpath ::
  Applicative f => TPath ->
  (Term -> f Term) -> Term -> f Term
tpath = foldl' (.) id . reverse . map tstep


(->:) :: StPath -> TPathStep -> StPath
(part, pa)->:s = (part, (s:pa))


stpart ::
  Applicative f => StPart ->
  (Term -> f Term) -> Status -> f Status
stpart (Assm v) = statusContext.aIx (FreeVar v)
stpart Thm      = statusTheorem
stpart Prf      = statusProof

stpath ::
  Applicative f => StPath ->
  (Term -> f Term) -> Status -> f Status
stpath (part, pa) = stpart part.tpath pa


-- not actually very useful - just for interface demo purposes!
swap :: StPath -> StPath -> Status -> Status
swap stpa stpa' = ap fromMaybe $ execStateT $ do
  guard $ not (snd stpa  `ancestor` snd stpa' ||
               snd stpa' `ancestor` snd stpa)
  a <- preuse (stpath stpa)  >>= lift
  b <- preuse (stpath stpa') >>= lift
  stpath stpa  .= b
  stpath stpa' .= a

