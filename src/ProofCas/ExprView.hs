{-# LANGUAGE RecursiveDo #-}
module ProofCas.ExprView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Text as T
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
    exprClick :: Event t StPath,
    exprDrag  :: Event t StPath,
    exprDrop  :: Event t StPath
  }

data RenderCtx t =
  RenderCtx {
    selection :: Demux t (Maybe StPath)
  }

type Render t m = WriterT [ExprEvents t] (ReaderT (RenderCtx t) m) ()

exprEvents ::
  Reflex t => StPath -> Event t a -> Event t b -> Event t c -> ExprEvents t
exprEvents stpa clickE dragE dropE =
  ExprEvents (stpa <$ clickE) (stpa <$ dragE) (stpa <$ dropE)

runRender :: Monad m => RenderCtx t -> Render t m -> m [ExprEvents t]
runRender ctx = flip runReaderT ctx . execWriterT


exprSpan ::
  (Reflex t, MonadWidget t m) => T.Text -> Render t m -> StPath -> Render t m
exprSpan exprType contents stpa = do
  selection <- asks selection
  rec
    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let selected = demuxed selection (Just stpa)

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
  let eEvs = exprEvents stpa clickedE dragE dropE
  tell [eEvs]

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

binder :: MonadWidget t m => T.Text -> DisplayExpr -> Render t m
binder v d =
  textSpan (T.concat ["(", v, " : "]) *> renderDExpr d <* textSpan ")"

renderDExpr :: MonadWidget t m => DisplayExpr -> Render t m
renderDExpr (NoPar stpa e) = renderDEL e stpa
renderDExpr (Par   stpa e) = textSpan "(" *> renderDEL e stpa <* textSpan ")"

renderDEL :: MonadWidget t m => DELevel DisplayExpr -> StPath -> Render t m
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

