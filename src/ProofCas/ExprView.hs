{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE CPP #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent, IsElement, IsEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif
import Data.Monoid
import Data.List
import qualified Data.Text as T
import Morte.Core hiding (Path)
import Control.Lens
import Control.Monad
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

exprSpan :: (Reflex t, MonadWidget t m) => T.Text -> Demux t (Maybe Path) -> m [Event t Path] -> Path -> m [Event t Path]
exprSpan exprType selection contents pa = do
  rec
    (span, es) <- elDynAttr' "span" attrs contents

    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    let selected = demuxed selection (Just pa)

    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let classes = classesFor $
         "expr-mouseover" =: hov <>
         "expr-dragenter" =: dragHov <>
         "expr-selected" =: selected

    let plainAttrs = constDyn $ "draggable" =: "true"
        attrs      = setClasses classes plainAttrs

  wrapDomEvent' (_element_raw span) Dragstart (setCurrentDragData "dummy" "dummy")
  wrapDomEvent' (_element_raw span) Dragover preventDefault
  clicked <- ownEvent Click span
  return $ (pa <$ clicked):es

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan content = elClass "span" "text" $ text content

binder selection v d = do
  textSpan $ T.concat ["(", v, " : "]
  es <- renderDExpr d selection
  textSpan ")"
  return es

renderDExpr :: MonadWidget t m => DisplayExpr -> Demux t (Maybe Path) -> m [Event t Path]
renderDExpr (NoPar pa e) selection = renderDEL e selection pa
renderDExpr (Par   pa e) selection = do
  textSpan "("
  renderDEL e selection pa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> Demux t (Maybe Path) -> Path -> m [Event t Path]
renderDEL DStar    selection = exprSpan "star" selection $ [] <$ textSpan "*"
renderDEL DBox     selection = exprSpan "box" selection $ [] <$ textSpan "\9633"
renderDEL (DVar v) selection = exprSpan "var" selection $ [] <$ textSpan v

renderDEL (DLam f l v d b) selection = exprSpan "lam" selection $ do
  when f $ textSpan "\955"
  es <- binder selection v d
  if l then textSpan " \8594 " else textSpan " "
  es' <- renderDExpr b selection
  return $ es ++ es'
renderDEL (DPi f l v d c) selection = exprSpan "pi" selection $ do
  when f $ textSpan "\8704"
  es <- binder selection v d
  if l then textSpan ", " else textSpan " "
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

exprWidget ::
  (Reflex t, MonadWidget t m, IsElement (RawElement d)) =>
  Expr X -> Element EventResult d t -> m ()
exprWidget e bodyEl = do
  rec
    eDyn <- foldDyn ($) e $ mergeWith (.) [eq]
    let body = widgetBody spc selection <$> eDyn
    clickedE <- el "div" (dyn body)
    clicked <- switchPromptly never clickedE
    selection <- foldDyn ($) Nothing $ mergeWith (.) [clicked, clickedW', spc]
    clickedW <- ownEvent Click bodyEl
    let clickedW' = const Nothing <$ clickedW
    let kp = domEvent Keydown bodyEl
        spc = fmap parent <$ ffilter (\n -> keyCodeLookup n == Space) kp
        eqKey = ffilter (\n -> keyCodeLookup n == Equals) kp
        eq = fforMaybe (tagPromptlyDyn selection eqKey) $ fmap (\sel -> path sel%~normalize)
  return ()

widgetBody spc selection e = do
  es <- renderDExpr (displayExpr e) (demux selection)
  return $ const . Just <$> leftmost es

