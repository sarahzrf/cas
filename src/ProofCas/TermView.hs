{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
module ProofCas.TermView where

import Reflex.Dom
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif
import Data.Monoid
import Data.List
import ProofCas.Hovering

data Term = Constant String | App Term [Term] | Infix String Term Term
  deriving (Show)

setCurrentDragData :: IsMouseEvent e => String -> EventM t e ()
#ifdef __GHCJS__
setCurrentDragData d = do
  e <- event
  Just dt <- getDataTransfer e
  setData dt "src" d
#else
setCurrentDragData _ = return ()
#endif

wrapDomEvent' el en a = do
  e <- wrapDomEvent el en a
  performEvent_ (return () <$ e)

termSpan :: (Reflex t, MonadWidget t m) => String -> m a -> m a
termSpan termType contents = do
  rec
    (span, a) <- elDynAttr' "span" attrs contents

    hovE <- hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_el_element span) (onEventName Drop) (False <$ stopPropagation)

    let dragHovE' = leftmost [dropE, dragHovE]
    classes <- classesFor $ "term-mouseover" =: hovE <> "term-dragenter" =: dragHovE'

    let plainAttrs = constDyn $ "draggable" =: "true"
    attrs <- setClasses classes plainAttrs

  wrapDomEvent' (_el_element span) (onEventName Dragstart) (setCurrentDragData "dummy")
  wrapDomEvent' (_el_element span) (onEventName Dragover) preventDefault
  return a

textSpan :: MonadWidget t m => String -> m ()
textSpan content = elClass "span" "text" $ text content

renderTerm :: MonadWidget t m => Term -> m ()
renderTerm (Constant name) = termSpan "constant" $ textSpan name
renderTerm (App f xs) = termSpan "app" $ do
  renderTerm f
  textSpan "("
  sequence_ $ intersperse (textSpan ", ") (map renderTerm xs)
  textSpan ")"
renderTerm (Infix op l r) = termSpan "infix" $ do
  renderTerm l
  textSpan (" " ++ op ++ " ")
  renderTerm r

