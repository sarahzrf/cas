{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
module ProofCas.Hovering where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement, IsEvent)
import GHCJS.DOM.EventM (eventTarget, eventCurrentTarget)
import Control.Applicative
import qualified Data.Text as T
import qualified Data.Map as Map
import Data.Monoid
import Data.Bool

eventWithIsOwn ::
  (MonadWidget t m, IsElement (RawElement d), IsEvent (EventType en)) =>
  EventName en -> Element EventResult d t -> m (Event t Bool)
eventWithIsOwn en el =
  wrapDomEvent (_element_raw el) (onEventName en)
    (liftA2 (==) eventTarget eventCurrentTarget)


hovering ::
  (MonadWidget t m, IsElement (RawElement d),
   IsEvent (EventType en), IsEvent (EventType en')) =>
  Element EventResult d t -> EventName en -> EventName en' -> m (Event t Bool)
hovering el leave over = do
  rec
    evL <- eventWithIsOwn leave el
    let evL' = fforMaybe evL $ bool Nothing (Just False)
    evO <- eventWithIsOwn over el
  let shouldHighlight = mergeWith (||) [evL', evO]
  return shouldHighlight


classesFor ::
  Reflex t => Map.Map T.Text (Dynamic t Bool) -> Dynamic t T.Text
classesFor =
  fmap (T.unwords . map fst . filter snd . Map.assocs) . sequenceA

addClasses ::
  Reflex t =>
  Dynamic t T.Text -> Dynamic t (Map.Map T.Text T.Text) ->
  Dynamic t (Map.Map T.Text T.Text)
addClasses = zipDynWith (flip Map.alter "class" . alterer)
  where alterer "" a        = a
        alterer c  Nothing  = Just c
        alterer c  (Just a) = Just (a <> " " <> c)

