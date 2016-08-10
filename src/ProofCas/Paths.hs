module ProofCas.Paths where

import Morte.Core hiding (Path)
import Control.Lens
import Data.List (foldl')

data PathStep =
  LamDom | LamBody | PiDom | PiCod | AppFunc | AppArg
  deriving (Eq, Ord, Show)

type Path = [PathStep]

parent :: Path -> Path
parent [] = []
parent (s:ss) = ss

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

