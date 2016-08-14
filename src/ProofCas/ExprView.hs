{-# LANGUAGE RecursiveDo #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Data.Monoid
import Data.List
import qualified Data.Text as T
import Morte.Core hiding (Path)
import Control.Lens
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import ProofCas.Hovering
import ProofCas.Pretty
import ProofCas.Paths
import ProofCas.SetDrag
import ProofCas.WriterInstances

wrapDomEvent' el en a = do
  e <- wrapDomEvent el (onEventName en) a
  performEvent_ (return () <$ e)

ownEvent ::
  (Reflex t, MonadWidget t m,
   IsElement (RawElement d), IsEvent (EventType en)) =>
  EventName en -> Element EventResult d t -> m (Event t Bool)
ownEvent en el = ffilter id <$> eventWithIsOwn en el


data ExprEvents t =
  ExprEvents {
    exprClick :: Event t Path,
    exprDrag  :: Event t Path,
    exprDrop  :: Event t Path
  }

data RenderCtx t =
  RenderCtx {
    selection :: Demux t (Maybe Path)
  }

type Render t m = WriterT [ExprEvents t] (ReaderT (RenderCtx t) m) ()

exprEvents ::
  Reflex t => Path -> Event t a -> Event t b -> Event t c -> ExprEvents t
exprEvents pa clickE dragE dropE =
  ExprEvents (pa <$ clickE) (pa <$ dragE) (pa <$ dropE)


exprSpan ::
  (Reflex t, MonadWidget t m) => T.Text -> Render t m -> Path -> Render t m
exprSpan exprType contents pa = do
  selection <- asks selection
  rec
    (span, _) <- elDynAttr' "span" attrs contents

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
  tell [eEvs]

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan content = elClass "span" "text" $ text content

binder v d = do
  textSpan $ T.concat ["(", v, " : "]
  es <- renderDExpr d
  textSpan ")"
  return es

renderDExpr :: MonadWidget t m => DisplayExpr -> Render t m
renderDExpr (NoPar pa e) = renderDEL e pa
renderDExpr (Par   pa e) = textSpan "(" *> renderDEL e pa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> Path -> Render t m
renderDEL DStar    = exprSpan "star" $ textSpan "*"
renderDEL DBox     = exprSpan "box" $ textSpan "\9633"
renderDEL (DVar v) = exprSpan "var" $ textSpan v

renderDEL (DLam f l v d b) = exprSpan "lam" $ do
  when f $ textSpan "\955"
  es <- binder v d
  if l then textSpan " \8594 " else textSpan " "
  renderDExpr b
renderDEL (DPi f l v d c) = exprSpan "pi" $ do
  when f $ textSpan "\8704"
  es <- binder v d
  if l then textSpan ", " else textSpan " "
  renderDExpr c
renderDEL (Arr d c) = exprSpan "arr" $ do
  es <- renderDExpr d
  textSpan " \8594 "
  renderDExpr c
renderDEL (DApp f a) = exprSpan "app" $ do
  es <- renderDExpr f
  textSpan " "
  renderDExpr a


exprWidget ::
  (Reflex t, MonadWidget t m, IsElement (RawElement d)) =>
  Expr X -> Element EventResult d t -> m ()
exprWidget e bodyEl = do
  rec
    eDyn <- foldDyn ($) e $ mergeWith (.) [eq, droppedE']
    let ctx = RenderCtx (demux selection)
        widgetBody = flip runReaderT ctx . execWriterT . renderDExpr . displayExpr
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

