{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif
import Data.Monoid
import Data.List
import qualified Data.Text as T
import Morte.Core hiding (Path)
import Control.Lens
import ProofCas.Hovering
import ProofCas.Pretty
import ProofCas.Paths

setCurrentDragData :: IsMouseEvent e => String -> String -> EventM t e ()
#ifdef __GHCJS__
setCurrentDragData k v = do
  e <- event
  Just dt <- getDataTransfer e
  setData dt k v
#else
setCurrentDragData _ _ = return ()
#endif

wrapDomEvent' el en a = do
  e <- wrapDomEvent el (onEventName en) a
  performEvent_ (return () <$ e)

exprSpan :: (Reflex t, MonadWidget t m) => T.Text -> Demux t Path -> m [Event t Path] -> Path -> m [Event t Path]
exprSpan exprType selection contents pa = do
  rec
    (span, es) <- elDynAttr' "span" attrs contents

    hovE <- hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    let selectedE = updated (demuxed selection pa)

    let dragHovE' = leftmost [dropE, dragHovE]
    classes <- classesFor $
      "expr-mouseover" =: hovE <>
      "expr-dragenter" =: dragHovE' <>
      "expr-selected" =: selectedE

    let plainAttrs = constDyn $ "draggable" =: "true"
        attrs      = setClasses classes plainAttrs

  wrapDomEvent' (_element_raw span) Dragstart (setCurrentDragData "dummy" "dummy")
  wrapDomEvent' (_element_raw span) Dragover preventDefault
  clicked <- ownEvent Click span
  return $ (pa <$ clicked):es

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan content = elClass "span" "text" $ text content

binder selection (v, d) = do
  textSpan $ T.concat ["(", v, " : "]
  es <- renderDExpr d selection
  textSpan ")"
  return es
binders selection = sequenceA . intersperse ([] <$ textSpan " ") . map (binder selection)

renderDExpr :: MonadWidget t m => DisplayExpr -> Demux t Path -> m [Event t Path]
renderDExpr (NoPar pa e) selection = renderDEL e selection pa
renderDExpr (Par   pa e) selection = do
  textSpan "("
  renderDEL e selection pa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> Demux t Path -> Path -> m [Event t Path]
renderDEL DStar    selection = exprSpan "star" selection $ [] <$ textSpan "*"
renderDEL DBox     selection = exprSpan "box" selection $ [] <$ textSpan "\9633"
renderDEL (DVar v) selection = exprSpan "var" selection $ [] <$ textSpan v

renderDEL (DLam p b) selection = exprSpan "lam" selection $ do
  textSpan "\955"
  es <- concat <$> binders selection p
  textSpan " \8594 "
  es' <- renderDExpr b selection
  return $ es ++ es'
renderDEL (DPi p c) selection = exprSpan "pi" selection $ do
  textSpan "\8704"
  es <- concat <$> binders selection p
  textSpan ", "
  es' <- renderDExpr c selection
  return $ es ++ es'
renderDEL (Arr d c) selection = exprSpan "arr" selection $ do
  es <- renderDExpr d selection
  textSpan " \8594 "
  es' <- renderDExpr c selection
  return $ es ++ es'
renderDEL (DApp f a) selection = exprSpan "app" selection $ do
  es <- renderDExpr f selection
  textSpan " "
  es' <- renderDExpr a selection
  return $ es ++ es'

exprWidget :: MonadWidget t m => Expr X -> m ()
exprWidget e = do
  rec
    eDyn <- foldDyn ($) e $ mergeWith (.) [eq]
    let body = widgetBody d spc selection <$> eDyn
    (d, clickedE) <- elAttr' "div" ("tabindex" =: "1") (dyn body)
    clicked <- switchPromptly never clickedE
    selection <- foldDyn ($) [] $ mergeWith (.) [clicked, spc]
    let kp = domEvent Keydown d
        spc = parent <$ ffilter (==32) kp
        eq = ffor (tagPromptlyDyn selection (ffilter (==61) kp)) $ \sel -> path sel%~normalize
  return ()

widgetBody d spc selection e = do
  es <- renderDExpr (displayExpr e) (demux selection)
  return $ const <$> leftmost es

