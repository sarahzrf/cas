{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE FlexibleContexts #-}
module ProofCas.Hovering where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import GHCJS.DOM.EventM (eventTarget, eventCurrentTarget)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Applicative
import Data.Monoid
import Data.Bool

eventWithIsOwn en el =
  wrapDomEvent (_el_element el) (onEventName en)
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
  Map String (Event t Bool) ->
  m (Dynamic t String)
classesFor events = do
  classesDyn <- foldDyn (<>) Map.empty (mergeMap events)
  forDyn classesDyn $ unwords . map fst . filter snd . Map.assocs

setClasses ::
  (Reflex t, MonadHold t m) =>
  Dynamic t String -> Dynamic t (Map String String) ->
  m (Dynamic t (Map String String))
setClasses = combineDyn (\classes attrs -> attrs <> "class" =: classes)

