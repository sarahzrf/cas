{-# LANGUAGE RecursiveDo #-}
module ProofCas.Hovering where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import GHCJS.DOM.EventM (eventTarget, eventCurrentTarget)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative
import qualified Data.Text as T
import Data.Monoid
import Data.Bool

eventWithIsOwn en el =
  wrapDomEvent (_element_raw el) (onEventName en)
    (liftA2 (==) eventTarget eventCurrentTarget)

ownEvent en el = do
  ev <- eventWithIsOwn en el
  return $ ffilter id ev

hovering el leave over = do
  rec
    evL <- eventWithIsOwn leave el
    let evL' = fforMaybe evL $ bool Nothing (Just False)
    evO <- eventWithIsOwn over el
  let shouldHighlight = mergeWith (||) [evL', evO]
  return shouldHighlight

classesFor ::
  (Reflex t, MonadWidget t m) =>
  Map T.Text (Event t Bool) ->
  m (Dynamic t T.Text)
classesFor events = do
  (fmap . fmap) (T.unwords . map fst . filter snd . Map.assocs) $
    foldDyn (<>) Map.empty (mergeMap events)

setClasses ::
  Reflex t =>
  Dynamic t T.Text -> Dynamic t (Map T.Text T.Text) ->
  Dynamic t (Map T.Text T.Text)
setClasses = zipDynWith (\classes attrs -> attrs <> "class" =: classes)

