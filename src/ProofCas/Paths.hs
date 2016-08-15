module ProofCas.Paths where

import Morte.Core hiding (Path)
import Control.Lens
import Control.Monad.State
import Data.List
import Data.Maybe

data PathStep =
  LamDom | LamBody | PiDom | PiCod | AppFunc | AppArg
  deriving (Eq, Ord, Show)

type Path = [PathStep]

parent :: Path -> Path
parent [] = []
parent (s:ss) = ss

ancestor :: Path -> Path -> Bool
ancestor = isSuffixOf


step :: Applicative f => PathStep ->
  (Expr a -> f (Expr a)) -> Expr a -> f (Expr a)
step LamDom  m (Lam v d b) = (\d -> Lam v d b) <$> m d
step LamBody m (Lam v d b) = (\b -> Lam v d b) <$> m b
step PiDom   m (Pi  v d c) = (\d -> Pi  v d c) <$> m d
step PiCod   m (Pi  v d c) = (\c -> Pi  v d c) <$> m c
step AppFunc m (App f a)   = (\f -> App f a)   <$> m f
step AppArg  m (App f a)   = (\a -> App f a)   <$> m a
step _ _ e = pure e

path :: Applicative f => Path ->
  (Expr a -> f (Expr a)) -> Expr a -> f (Expr a)
path = foldl' (.) id . reverse . map step


-- not actually very useful - just for interface demo purposes!
swap :: Path -> Path -> Expr a -> Expr a
swap pa pa' = ap fromMaybe $ execStateT $ do
  guard $ not (pa `ancestor` pa' || pa' `ancestor` pa)
  a <- preuse (path pa) >>= lift
  b <- preuse (path pa') >>= lift
  path pa  .= b
  path pa' .= a

