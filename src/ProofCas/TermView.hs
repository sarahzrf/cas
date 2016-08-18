{-# LANGUAGE RecursiveDo #-}
module ProofCas.TermView where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Utils.Pretty
import Utils.ABT
import Utils.Plicity
import Utils.Telescope
import DependentImplicit.Core.Term
import Control.Monad.Reader
import Control.Monad.Writer
import Data.List
import Data.Maybe
import qualified Data.Text as T
import ProofCas.Hovering
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


data TermEvents t =
  TermEvents {
    termClick :: Event t StPath,
    termDrag  :: Event t StPath,
    termDrop  :: Event t StPath
  }

data RenderCtx t =
  RenderCtx {
    selection :: Demux t (Maybe StPath)
  }

type Render t m = WriterT [TermEvents t] (ReaderT (RenderCtx t) m) ()

termEvents ::
  Reflex t => StPath -> Event t a -> Event t b -> Event t c -> TermEvents t
termEvents stpa clickE dragE dropE =
  TermEvents (stpa <$ clickE) (stpa <$ dragE) (stpa <$ dropE)

runRender :: Monad m => RenderCtx t -> Render t m -> m [TermEvents t]
runRender ctx = flip runReaderT ctx . execWriterT


termSpan ::
  (Reflex t, MonadWidget t m) => T.Text -> StPath -> Render t m -> Render t m
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

        plainAttrs = constDyn $ "draggable" =: "true"
        attrs      = setClasses classes plainAttrs

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

wrapP :: MonadWidget t m => Bool -> Plicity -> m a -> m a
wrapP True  Expl = bracket "(" ")"
wrapP False Expl = id
wrapP _     Impl = bracket "{" "}"


parenthesizeTerm, renderTerm :: MonadWidget t m => Term -> StPath -> Render t m
parenthesizeTerm t stpa
  | (l:_) <- _tpathPart stpa,
    parenLoc t l = body
  | otherwise = bracket "(" ")" body
  where body = renderTerm t stpa
renderTerm (Var v) stpa = termSpan "var" stpa . textSpan . T.pack . name $ v
renderTerm (In (Defined v)) stpa = termSpan "var" stpa . textSpan . T.pack $ v
renderTerm (In (Ann t y)) stpa = termSpan "ann" stpa $ do
  parenthesizeTerm (instantiate0 t) (stpa->:AnnTerm)
  textSpan " : "
  parenthesizeTerm (instantiate0 y) (stpa->:AnnType)
renderTerm (In Type) stpa = termSpan "typ" stpa $ textSpan "Type"
renderTerm (In (Fun p d c)) stpa = termSpan "fun" stpa $ do
  wrapP True p $ do
    textSpan $ T.pack (unwords (names c)) <> " : "
    parenthesizeTerm (instantiate0 d) (stpa->:FunArg)
  textSpan " \8594 "
  parenthesizeTerm (body c) (stpa->:FunRet)
renderTerm (In (Lam p b)) stpa = termSpan "lam" stpa $ do
  textSpan "\955"
  wrapP False p . textSpan . T.pack . unwords . names $ b
  textSpan " \8594 "
  parenthesizeTerm (body b) (stpa->:LamBody)
renderTerm (In (App p f a)) stpa = termSpan "app" stpa $ do
  parenthesizeTerm (instantiate0 f) (stpa->:AppFun)
  textSpan " "
  wrapP False p $ parenthesizeTerm (instantiate0 a) (stpa->:AppArg p)
renderTerm (In (Con i [])) stpa = termSpan "con" stpa . textSpan . T.pack $ i
renderTerm (In (Con i a)) stpa = termSpan "con" stpa $ do
  textSpan $ T.pack i <> " "
  sepBy_ " " (zip [0..] a) $ \(n, (p, a)) ->
    wrapP False p $ parenthesizeTerm (instantiate0 a) (stpa->:ConArg p n)
renderTerm (In (Case a o c)) stpa = termSpan "cas" stpa $ do
  textSpan "case "
  sepBy_ " || " (zip [0..] a) $ \(n, a) ->
    parenthesizeTerm (instantiate0 a) (stpa->:CaseArg n)

  textSpan " motive "
  let CaseMotive (BindingTelescope b r) = o
  forM_ (zip3 [0..] b (names r)) $ \(n, b, v) -> do
    textSpan $ "(" <> T.pack v <> " : "
    parenthesizeTerm (body b) (stpa->:MotiveArg n)
    textSpan ") || "
  parenthesizeTerm (body r) (stpa->:MotiveRet)

  textSpan " of "
  sepBy_ " | " (zip [0..] c) $ \(n, Clause p r) -> do
    textSpan $ T.pack . intercalate " || " . map (pretty.body.unwrapPatternF.fmap body) $ p
    textSpan " \8594 "
    parenthesizeTerm (body r) (stpa->:ClauseBody n)

  textSpan " end"

