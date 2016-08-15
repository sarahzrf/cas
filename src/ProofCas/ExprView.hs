{-# LANGUAGE RecursiveDo #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Text as T
import Morte.Core hiding (Path)
import Control.Lens
import ProofCas.Hovering
import ProofCas.Pretty
import ProofCas.Paths
import ProofCas.SetDrag
import ProofCas.WriterInstances

wrapDomEvent' ::
  (IsElement e, PerformEvent t m, TriggerEvent t m) =>
  e -> EventName en -> EventM e (EventType en) b -> m ()
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

    (span, _) <- elDynAttr' "span" attrs contents

  wrapDomEvent' (_element_raw span) Dragover preventDefault
  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy" >> stopPropagation)
  clickedE <- ownEvent Click span
  let eEvs = exprEvents pa clickedE dragE dropE
  tell [eEvs]

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

binder :: MonadWidget t m => T.Text -> DisplayExpr -> Render t m
binder v d =
  textSpan (T.concat ["(", v, " : "]) *> renderDExpr d <* textSpan ")"

renderDExpr :: MonadWidget t m => DisplayExpr -> Render t m
renderDExpr (NoPar pa e) = renderDEL e pa
renderDExpr (Par   pa e) = textSpan "(" *> renderDEL e pa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> Path -> Render t m
renderDEL DStar    = exprSpan "star" $ textSpan "*"
renderDEL DBox     = exprSpan "box" $ textSpan "\9633"
renderDEL (DVar v) = exprSpan "var" $ textSpan v

renderDEL (DLam f l v d b) = exprSpan "lam" $ do
  when f $ textSpan "\955"
  binder v d
  if l then textSpan " \8594 " else textSpan " "
  renderDExpr b
renderDEL (DPi f l v d c) = exprSpan "pi" $ do
  when f $ textSpan "\8704"
  binder v d
  if l then textSpan ", " else textSpan " "
  renderDExpr c
renderDEL (Arr d c) = exprSpan "arr" $ do
  renderDExpr d
  textSpan " \8594 "
  renderDExpr c
renderDEL (DApp f a) = exprSpan "app" $ do
  renderDExpr f
  textSpan " "
  renderDExpr a


fromUpdates :: MonadWidget t m => a -> [Event t (a -> a)] -> m (Dynamic t a)
fromUpdates initial updaters = foldDyn ($) initial (mergeWith (.) updaters)

exprWidget ::
  (MonadWidget t m, IsElement (RawElement d)) =>
  Expr X -> Element EventResult d t -> m ()
exprWidget e bodyEl = do
  rec
    let exprEvE which = switchPromptly never $ leftmost . map which <$> exprEvsE
    clickedE <- exprEvE exprClick
    draggedE <- exprEvE exprDrag
    droppedE <- exprEvE exprDrop
    clickedW <- ownEvent Click bodyEl
    let keybind k = ffilter (\n -> keyCodeLookup n == k) (domEvent Keydown bodyEl)

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        up    = fmap parent <$ keybind Space
    selection <- fromUpdates Nothing [sel, desel, up]

    dragging <- holdDyn [] draggedE
    let -- this will break if you drop other random shit from outside... hmm
        drop  = uncurry swap <$> dragging `attachPromptlyDyn` droppedE
        norm  = fmap (\sel -> path sel%~normalize) `fmapMaybe` tagPromptlyDyn selection (keybind Equals)
    eDyn <- fromUpdates e [norm, drop]

    let ctx = RenderCtx (demux selection)
        widgetBody = flip runReaderT ctx . execWriterT . renderDExpr . displayExpr
    exprEvsE <- el "div" $ dyn (widgetBody <$> eDyn)
  return ()

