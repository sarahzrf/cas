{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
module ProofCas.ExprView where

import Reflex.Dom
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif
import Data.Monoid
import Data.List
import Data.Foldable
import ProofCas.Hovering
import ProofCas.Pretty

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

binders :: MonadWidget t m => [(String, DisplayExpr)] -> m ()
binder (v, d) = do
  textSpan $ "(" ++ v ++ " : "
  renderDExpr d
  textSpan ")"
binders = sequenceA_ . intersperse (textSpan " ") . map binder

renderDExpr :: MonadWidget t m => DisplayExpr -> m ()
renderDExpr (NoPar pa e) = renderDEL e
renderDExpr (Par   pa e) = do
  textSpan "("
  renderDEL e
  textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> m ()
renderDEL DStar    = exprSpan "star" $ textSpan "*"
renderDEL DBox     = exprSpan "box"  $ textSpan "\9633"
renderDEL (DVar v) = exprSpan "var" $ textSpan v

renderDEL (DLam p b) = exprSpan "lam" $ do
  textSpan "\955"
  binders p
  textSpan " \8594 "
  renderDExpr b
renderDEL (DPi p c) = exprSpan "pi" $ do
  textSpan "\8704"
  binders p
  textSpan ", "
  renderDExpr c
renderDEL (Arr d c) = exprSpan "arr" $ do
  renderDExpr d
  textSpan " \8594 "
  renderDExpr c
renderDEL (DApp f a) = exprSpan "app" $ do
  renderDExpr f
  textSpan " "
  renderDExpr a

