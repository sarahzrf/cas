{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module ProofCas.TermView where

import Reflex.Dom
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif
import Morte.Core
import Data.Text.Lazy
import Data.Monoid
import Data.List
import ProofCas.Hovering

setCurrentDragData :: IsMouseEvent e => String -> EventM t e ()
#ifdef __GHCJS__
setCurrentDragData d = do
  e <- event
  Just dt <- getDataTransfer e
  setData dt ("src" :: String) d
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

renderTerm :: MonadWidget t m => Expr X -> m ()
renderTerm (Const Star) = termSpan "const" $ textSpan "*"
renderTerm (Const Box)  = termSpan "const" $ textSpan "\9633"
renderTerm (Var v)      = termSpan "var" $ textSpan (unpack (pretty v))
renderTerm (Embed x)    = absurd x

renderTerm (Lam v d b) = termSpan "lam" $ do
  textSpan $ "\955(" ++ unpack v ++ " : "
  renderTerm d
  textSpan ") \8594 "
  renderTerm b
renderTerm (Pi "_" d c) = termSpan "pi" $ do
  renderTerm d
  textSpan " \8594 "
  renderTerm c
renderTerm (Pi v d c) = termSpan "pi" $ do
  textSpan $ "\8704(" ++ unpack v ++ " : "
  renderTerm d
  textSpan "), "
  renderTerm c
renderTerm (App f a) = termSpan "app" $ do
  textSpan "("
  renderTerm f
  textSpan " "
  renderTerm a
  textSpan ")"

