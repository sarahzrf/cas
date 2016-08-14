{-# LANGUAGE RecursiveDo #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement)
import Data.Monoid
import Data.List
import qualified Data.Text as T
import Morte.Core hiding (Path)
import Control.Lens
import Control.Monad
import ProofCas.Hovering
import ProofCas.Pretty
import ProofCas.Paths
import ProofCas.SetDrag

data ExprEvents t =
  ExprEvents {
    exprClick :: Event t Path,
    exprDrag  :: Event t Path,
    exprDrop  :: Event t Path
  }

exprEvents ::
  Reflex t => Path -> Event t a -> Event t b -> Event t c -> ExprEvents t
exprEvents pa clickE dragE dropE =
  ExprEvents (pa <$ clickE) (pa <$ dragE) (pa <$ dropE)

wrapDomEvent' el en a = do
  e <- wrapDomEvent el (onEventName en) a
  performEvent_ (return () <$ e)

exprSpan ::
  (Reflex t, MonadWidget t m) =>
  T.Text -> Demux t (Maybe Path) ->
  m [ExprEvents t] -> Path -> m [ExprEvents t]
exprSpan exprType selection contents pa = do
  rec
    (span, es) <- elDynAttr' "span" attrs contents

    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let selected = demuxed selection (Just pa)

    let classes = classesFor $
         "expr-mouseover" =: hov <>
         "expr-dragenter" =: dragHov <>
         "expr-selected" =: selected

        plainAttrs = constDyn $ "draggable" =: "true"
        attrs      = setClasses classes plainAttrs

  wrapDomEvent' (_element_raw span) Dragover preventDefault
  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy" >> stopPropagation)
  clickedE <- ownEvent Click span
  let eEvs = exprEvents pa clickedE dragE dropE
  return $ eEvs:es

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan content = elClass "span" "text" $ text content

binder selection v d = do
  textSpan $ T.concat ["(", v, " : "]
  es <- renderDExpr d selection
  textSpan ")"
  return es

renderDExpr :: MonadWidget t m => DisplayExpr -> Demux t (Maybe Path) -> m [ExprEvents t]
renderDExpr (NoPar pa e) selection = renderDEL e selection pa
renderDExpr (Par   pa e) selection = do
  textSpan "("
  renderDEL e selection pa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> Demux t (Maybe Path) -> Path -> m [ExprEvents t]
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
    eDyn <- foldDyn ($) e $ mergeWith (.) [eq, droppedE']
    let widgetBody e = renderDExpr (displayExpr e) (demux selection)
        body = widgetBody <$> eDyn
    exprEvsE <- el "div" (dyn body)

    clickedE <- switchPromptly never $ leftmost . map exprClick <$> exprEvsE
    draggedE <- switchPromptly never $ leftmost . map exprDrag  <$> exprEvsE
    droppedE <- switchPromptly never $ leftmost . map exprDrop  <$> exprEvsE
    clickedW <- ownEvent Click bodyEl

    dragging <- holdDyn [] draggedE
    let clickedE' = const . Just <$> clickedE
        clickedW' = const Nothing <$ clickedW
        -- this will break if you drop other random shit from outside... hmm
        droppedE' = uncurry swap <$> dragging `attachPromptlyDyn` droppedE
    let kp = domEvent Keydown bodyEl
        spc = fmap parent <$ ffilter (\n -> keyCodeLookup n == Space) kp
        eqKey = ffilter (\n -> keyCodeLookup n == Equals) kp
        eq = fforMaybe (tagPromptlyDyn selection eqKey) $ fmap (\sel -> path sel%~normalize)

    selection <- foldDyn ($) Nothing $ mergeWith (.) [clickedE', clickedW', spc]
  return ()

