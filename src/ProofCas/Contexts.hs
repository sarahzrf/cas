module ProofCas.Contexts where

import Morte.Context
import Control.Lens hiding (Context)
import Control.Monad.State
import qualified Data.Text.Lazy as TL
import qualified Data.Map as Map

type NContext a = [((TL.Text, Int), a)]

numberContext :: Context a -> NContext a
numberContext ctx =
  flip evalState Map.empty . forM (toList ctx) $ \(v, a) -> do
    occ <- use (at v.non 0)
    at v.non 0 += 1
    return ((v, occ), a)

denumberContext :: NContext a -> Context a
denumberContext = Context . map (_1%~fst)

numbered :: Lens (Context a) (Context b) (NContext a) (NContext b)
numbered = iso numberContext denumberContext

aIx :: (Eq k, Applicative f) => k -> (a -> f a) -> [(k, a)] -> f [(k, a)]
aIx k m [] = pure []
aIx k m ((k', a):kas)
  | k == k' = (\a' -> (k', a'):kas) <$> m a
  | otherwise = ((k', a):) <$> aIx k m kas

