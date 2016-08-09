{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
module ProofCas.ExprView where

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

exprSpan :: (Reflex t, MonadWidget t m) => String -> m a -> m a
exprSpan exprType contents = do
  rec
    (span, a) <- elDynAttr' "span" attrs contents

    hovE <- hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_el_element span) (onEventName Drop) (False <$ stopPropagation)

    let dragHovE' = leftmost [dropE, dragHovE]
    classes <- classesFor $ "expr-mouseover" =: hovE <> "expr-dragenter" =: dragHovE'

    let plainAttrs = constDyn $ "draggable" =: "true"
    attrs <- setClasses classes plainAttrs

  wrapDomEvent' (_el_element span) (onEventName Dragstart) (setCurrentDragData "dummy")
  wrapDomEvent' (_el_element span) (onEventName Dragover) preventDefault
  return a

textSpan :: MonadWidget t m => String -> m ()
textSpan content = elClass "span" "text" $ text content

renderExpr :: MonadWidget t m => Expr X -> m ()
renderExpr (Const Star) = exprSpan "const" $ textSpan "*"
renderExpr (Const Box)  = exprSpan "const" $ textSpan "\9633"
renderExpr (Var v)      = exprSpan "var" $ textSpan (unpack (pretty v))
renderExpr (Embed x)    = absurd x

renderExpr (Lam v d b) = exprSpan "lam" $ do
  textSpan $ "\955(" ++ unpack v ++ " : "
  renderExpr d
  textSpan ") \8594 "
  renderExpr b
renderExpr (Pi "_" d c) = exprSpan "pi" $ do
  renderExpr d
  textSpan " \8594 "
  renderExpr c
renderExpr (Pi v d c) = exprSpan "pi" $ do
  textSpan $ "\8704(" ++ unpack v ++ " : "
  renderExpr d
  textSpan "), "
  renderExpr c
renderExpr (App f a) = exprSpan "app" $ do
  textSpan "("
  renderExpr f
  textSpan " "
  renderExpr a
  textSpan ")"

