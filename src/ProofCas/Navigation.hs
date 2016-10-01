{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
module ProofCas.Navigation where

import Control.Lens
import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Maybe
import Data.List

type Tree p id = M.Map (p, id) (Maybe id, [id])

type Movement p id a = (Ord p, Ord id) => StateT (p, id) (ReaderT (Tree p id) Maybe) a

runMovement :: (Ord p, Ord id) => Movement p id a -> Tree p id -> Maybe (p, id) -> Maybe (p, id)
runMovement m tree = fmap $ \pid -> fromMaybe pid $ runReaderT (execStateT m pid) tree


try :: Movement p id a -> Movement p id Bool
try m = True <$ m <|> return False

upwards :: Movement p id ()
upwards = do
  tree <- ask
  cur <- get
  (mpar, _) <- lift . lift $ M.lookup cur tree
  par <- lift . lift $ mpar
  _2 .= par

downwards :: ([id] -> Maybe id) -> Movement p id ()
downwards pick = do
  tree <- ask
  cur <- get
  (_, children) <- lift . lift $ M.lookup cur tree
  child <- lift . lift $ pick children
  _2 .= child

sideways :: (Int -> Int) -> Movement p id ()
sideways ixF = do
  tree <- ask
  cur@(part, cid) <- get
  sib <- lift . lift $ do
    (mpar, _) <- M.lookup cur tree
    par <- mpar
    (_, sibs) <- M.lookup (part, par) tree
    selIx <- findIndex (==cid) sibs
    sibs^?ix (ixF selIx)
  _2 .= sib

firstborn, youngest, left, right :: Movement p id ()
firstborn = downwards (preview _head)
youngest  = downwards (preview _last)
left  = sideways (subtract 1)
right = sideways (+1)


data Era = Early | Late

other :: Era -> Era
other Early = Late
other Late  = Early

sidewaysD, downwardsD :: Era -> Movement p id ()
sidewaysD  Early = left
sidewaysD  Late  = right
downwardsD Early = firstborn
downwardsD Late  = youngest


sibLeaf :: Era -> Movement p id ()
sibLeaf era = do
  u <- try . fix $ \ascend -> do s <- try (sidewaysD era); unless s (upwards >> ascend)
  let era' = if u then other era else era
  fix $ \descend -> do d <- try (downwardsD era'); when d descend

prevLeaf, nextLeaf :: Movement p id ()
prevLeaf = sibLeaf Early
nextLeaf = sibLeaf Late

