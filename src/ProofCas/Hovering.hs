{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}
module ProofCas.Hovering where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import GHCJS.DOM.EventM (eventTarget, eventCurrentTarget)
import qualified Data.Map as Map
import Control.Applicative
import Data.Monoid

eventWithIsOwn en el =
  wrapDomEvent (_el_element el) (onEventName en)
    (liftA2 (==) eventTarget eventCurrentTarget)

hovering el leave over = do
  rec
    evL <- eventWithIsOwn leave el
    let evL' = fforMaybe evL $ \own -> if own then Just False else Nothing
    evO <- eventWithIsOwn over el
  let shouldHighlight = mergeWith (||) [evL', evO]
  return shouldHighlight

classesFor ::
  (Reflex t, MonadWidget t m) =>
  Map.Map String (Event t Bool) ->
  m (Dynamic t String)
classesFor events = do
  classesDyn <- foldDyn (<>) Map.empty (mergeMap events)
  forDyn classesDyn $ unwords . map fst . filter snd . Map.assocs

setClasses ::
  (Reflex t, MonadHold t m) =>
  Dynamic t String -> Dynamic t (Map.Map String String) ->
  m (Dynamic t (Map.Map String String))
setClasses = combineDyn (\classes attrs -> attrs <> "class" =: classes)

