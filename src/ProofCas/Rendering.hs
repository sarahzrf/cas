{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections #-}
module ProofCas.Rendering where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Control.Lens
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor.Foldable
import Data.Functor.Compose
import Data.List
import Data.Maybe
import qualified Data.Text as T
import ProofCas.Rendering.Hovering
import ProofCas.Rendering.SetDrag
import ProofCas.Rendering.WriterInstances

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


data TermEvents t pa =
  TermEvents {
    termClick :: Event t (StPart, pa),
    termDrag  :: Event t (StPart, pa),
    termDrop  :: Event t (StPart, pa)
  }

data RenderCtx t pa =
  RenderCtx {
    selection :: Demux t (Maybe (StPart, pa))
  }

type Render t pa m = WriterT [TermEvents t pa] (ReaderT (RenderCtx t pa) m) ()

termEvents ::
  Reflex t => (StPart, pa)-> Event t a -> Event t b -> Event t c -> TermEvents t pa
termEvents stpa clickE dragE dropE =
  TermEvents (stpa <$ clickE) (stpa <$ dragE) (stpa <$ dropE)

runRender :: Monad m => RenderCtx t pa -> Render t pa m -> m [TermEvents t pa]
runRender ctx = flip runReaderT ctx . execWriterT


termSpan ::
  (Reflex t, MonadWidget t m, Eq pa) => T.Text -> (StPart, pa) -> Render t pa m -> Render t pa m
termSpan termType stpa contents = do
  selection <- asks selection
  rec
    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let selected = demuxed selection (Just stpa)

    let classes = classesFor $
         "term-mouseover" =: hov <>
         "term-dragenter" =: dragHov <>
         "term-selected" =: selected

        plainAttrs = constDyn $ "draggable" =: "true" <> "class" =: termType
        attrs      = addClasses classes plainAttrs

    (span, _) <- elDynAttr' "span" attrs contents

  wrapDomEvent' (_element_raw span) Dragover preventDefault
  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy" >> stopPropagation)
  clickedE <- ownEvent Click span
  let eEvs = termEvents stpa clickedE dragE dropE
  tell [eEvs]


textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

sepBy :: MonadWidget t m => T.Text -> [a] -> (a -> m b) -> m [b]
sepBy sep as f = fmap catMaybes . sequence . intersperse sepM . map f' $ as
  where sepM = Nothing <$ textSpan sep
        f'   = fmap Just . f

sepBy_ :: MonadWidget t m => T.Text -> [a] -> (a -> m b) -> m ()
sepBy_ sep as f = void $ sepBy sep as f

bracket :: MonadWidget t m => T.Text -> T.Text -> m a -> m a
bracket o c m = textSpan o *> m <* textSpan c


type Renderable e f pa =
  (Recursive e, Base e ~ Compose ((,) pa) f, Functor f, Ord pa)

renderTerm ::
  (Renderable e f pa, MonadWidget t m) =>
  (f e -> f (e, Bool)) ->
  (f e -> T.Text) ->
  (f (Render t pa m) -> Render t pa m) ->
  StPart -> e -> Render t pa m
renderTerm prec cls step part = go
  where
    go e = termSpan (cls t) (part, pa) $ step subterms
      where Compose (pa, t) = project e
            subterms = prec t <&> \(sub, par) -> (if par then bracket "(" ")" else id) (go sub)


data DStatus e =
  DStatus {
    _dstatusContext :: [(String, e)],
    _dstatusTheorem :: e
  }

data StPart =
  Assm String | Thm | Prf
  deriving (Eq, Ord, Show)

proofCasWidget ::
  (Renderable e f pa, MonadWidget t m) =>
  (f e -> f (e, Bool)) ->
  (f e -> T.Text) ->
  (f (Render t pa m) -> Render t pa m) ->
  Dynamic t (DStatus e) ->
  Dynamic t (Maybe (StPart, pa)) ->
  m (Event t (StPart, pa), Event t ((StPart, pa), (StPart, pa)))
proofCasWidget prec cls step dstDyn selection = do
  let ctx = RenderCtx (demux selection)
  (div, termEvsE) <- el' "div" . dyn . ffor dstDyn $ \st -> runRender ctx $ do
    forM (_dstatusContext st) $ \(v, de) -> do
      textSpan $ T.pack v <> " : "
      renderTerm prec cls step (Assm v) de
      el "br" $ return ()
    el "hr" $ return ()
    renderTerm prec cls step Thm (_dstatusTheorem st)

  let termEvE which = switchPromptly never $ leftmost . map which <$> termEvsE
  clickedE <- termEvE termClick
  draggedE <- termEvE termDrag
  droppedE <- termEvE termDrop

  dragging <- holdDyn Nothing (leftmost [Nothing <$ domEvent Dragend div, Just <$> draggedE])
  let dropsE = attachPromptlyDynWithMaybe (\g r -> (,r) <$> g) dragging droppedE

  return (clickedE, dropsE)

