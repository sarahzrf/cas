{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
module ProofCas.Rendering where

import Reflex.Dom hiding (preventDefault, stopPropagation)
import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Control.Lens
import Control.Lens.Internal.Context (sell)
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Applicative
import Data.List
import qualified Data.Map as M
import qualified Data.List.NonEmpty as N
import Data.Maybe
import qualified Data.Text as T
import Data.String
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


type P id = (StPart, id)

type Tree id = M.Map (P id) (Maybe id, [id])

data RenderRes t id =
  RenderRes {
    termClicks :: [Event t (P id)],
    termDrags  :: [Event t (P id)],
    termDrops  :: [Event t (P id)],
    tree       :: Tree id
  }

instance Ord id => Monoid (RenderRes t id) where
  mempty = RenderRes mempty mempty mempty mempty
  mappend (RenderRes tc td td_ t) (RenderRes tc' td' td_' t') = RenderRes (tc <> tc') (td <> td') (td_ <> td_') (t <> t')

data RenderCtx t id =
  RenderCtx {
    selection :: Demux t (Maybe (P id))
  }

type Render  t id m = (MonadWriter (RenderRes t id) m, MonadReader (RenderCtx t id) m, MonadWidget t m)
type RenderM t id m = WriterT (RenderRes t id) (ReaderT (RenderCtx t id) m)

renderRes ::
  Reflex t => P id -> Event t a -> Event t b -> Event t c -> RenderRes t id
renderRes stid clickE dragE dropE =
  RenderRes [stid <$ clickE] [stid <$ dragE] [stid <$ dropE] M.empty

execRender :: Monad m => RenderCtx t id -> RenderM t id m a -> m (RenderRes t id)
execRender ctx = flip runReaderT ctx . execWriterT


termSpan ::
  (Reflex t, Ord id, Render t id m) => P id -> T.Text -> m a -> m a
termSpan stid termType contents = do
  selection <- asks selection
  rec
    hov <- holdDyn False =<< hovering span Mouseleave Mouseover
    dragHovE <- hovering span Dragleave Dragenter
    dropE <- wrapDomEvent (_element_raw span) (onEventName Drop) (False <$ stopPropagation)
    dragHov <- holdDyn False $ leftmost [dropE, dragHovE]
    let selected = demuxed selection (Just stid)

    let classes = classesFor $
         "term-mouseover" =: hov <>
         "term-dragenter" =: dragHov <>
         "term-selected" =: selected

        plainAttrs = constDyn $ "draggable" =: "true" <> "class" =: termType
        attrs      = addClasses classes plainAttrs

    (span, a) <- elDynAttr' "span" attrs contents

  wrapDomEvent' (_element_raw span) Dragover preventDefault
  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy" >> stopPropagation)
  clickedE <- ownEvent Click span
  tell $ renderRes stid clickedE dragE dropE
  return a


textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

bracket :: MonadWidget t m => T.Text -> T.Text -> m a -> m a
bracket o c m = textSpan o *> m <* textSpan c


newtype RenderLayer a = RenderLayer {
  runRL :: forall t m. MonadWidget t m => Bazaar (->) a (m ()) (m ())
}

instance Functor RenderLayer where
  fmap f rl = RenderLayer (runRL rl & loci%~f)

instance Monoid (RenderLayer a) where
  mempty = RenderLayer (pure (return ()))
  mappend x y = RenderLayer (liftA2 (>>) (runRL x) (runRL y))

instance IsString (RenderLayer a) where
  fromString s = RenderLayer (pure (textSpan (T.pack s)))

rlel :: T.Text -> RenderLayer a -> RenderLayer a
rlel y rl = RenderLayer (el y <$> runRL rl)

rlrec :: a -> RenderLayer a
rlrec a = RenderLayer (sell a)

sepBy :: Monoid m => m -> [m] -> m
sepBy sep = mconcat . intersperse sep

data DTerm id =
  DTerm {
    termType :: T.Text,
    termId :: id,
    parenthesize :: Bool,
    render :: RenderLayer (DTerm id)
  }

renderTerm ::
  (Ord id, Render t id m) =>
  StPart -> DTerm id -> m ()
renderTerm part = go Nothing
  where
    go parent dt = (if parenthesize dt then bracket "(" ")" else id) $ do
      let me = termId dt
          (children, body) = runBazaar (runRL (render dt)) (\subterm -> ([termId subterm], go (Just me) subterm))
      termSpan (part, me) (termType dt) body
      tell mempty{tree=(part, me) =: (parent, children)}


data DStatus e =
  DStatus {
    _dstatusContext :: [(String, e)],
    _dstatusTheorem :: e
  } deriving Functor

data StPart =
  Assm String | Thm | Prf
  deriving (Eq, Ord, Show)

keybind :: Reflex t => Element EventResult d t -> Key -> Event t Key
keybind bodyEl k = ffilter (==k) (keyCodeLookup <$> domEvent Keydown bodyEl)

fromUpdates :: MonadWidget t m => a -> [Event t (a -> a)] -> m (Dynamic t a)
fromUpdates initial updaters = foldDyn ($) initial (mergeWith (.) updaters)

ifN _ m@(Just _) = m
ifN m _ = m

parent :: Ord id => Tree id -> Maybe (P id) -> Maybe (P id)
parent tree msel = do
  sel@(part, _) <- msel
  (mpar, _) <- M.lookup sel tree
  par <- mpar
  return (part, par)

child :: Ord id => ([id] -> Maybe id) -> Tree id -> Maybe (P id) -> Maybe (P id)
child which tree msel = do
  sel@(part, _) <- msel
  (_, children) <- M.lookup sel tree
  first <- which children
  return (part, first)

sib :: Ord id => (Int -> Int) -> ([id] -> Maybe id) -> Bool -> Tree id -> Maybe (P id) -> Maybe (P id)
sib ixF which base tree msel = do
  sel@(part, selId) <- msel
  (mpar, _) <- M.lookup sel tree
  par <- mpar
  (_, sibs) <- M.lookup (part, par) tree
  selIx <- findIndex (==selId) sibs
  -- case sibs^?ix (ixF selIx) of Nothing -> child which tree msel; Just sib -> return (part, sib)
  (part,) <$> sibs^?ix (ixF selIx) <|>
    (parent tree msel & sib ixF which False tree) <|>
    (guard base >> child which tree msel)

proofCasWidget ::
  (Ord id, MonadWidget t m, IsElement (RawElement d)) =>
  Dynamic t (DStatus (DTerm id)) ->
  Element EventResult d t ->
  Event t (N.NonEmpty String) ->
  m (Dynamic t (Maybe (P id)), Event t (P id, P id))
proofCasWidget dstDyn bodyEl errE = do
  rec
    errors <- foldDyn (++) [] (map T.pack . N.toList <$> errE)
    let ctx = RenderCtx (demux selection)
    (div, termEvsE) <- elClass' "div" "cas" $ do
      termEvsE <- dyn . ffor dstDyn $ \st -> execRender ctx $ do
        elClass "div" "assms" $ el "ul" $ do
          forM_ (_dstatusContext st) $ \(v, dt) -> el "li" $ do
            textSpan $ T.pack v <> " : "
            renderTerm (Assm v) dt
        el "hr" $ return ()
        elClass "div" "thm" $
          renderTerm Thm (_dstatusTheorem st)
      el "hr" $ return ()
      elClass "div" "errors" $ el "ul" $ do
        dyn . ffor errors $ \es -> do
          forM_ es $ elClass "li" "error" . textSpan
      return termEvsE

    let termEvE which = switchPromptly never $ leftmost . which <$> termEvsE
    clickedE <- termEvE termClicks
    draggedE <- termEvE termDrags
    droppedE <- termEvE termDrops
    treeD    <- holdDyn M.empty (tree <$> termEvsE)
    clickedW <- ownEvent Click bodyEl

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        up    = parent <$> tagPromptlyDyn treeD (keybind bodyEl ArrowUp)
        down  = child (^?_head) <$> tagPromptlyDyn treeD (keybind bodyEl ArrowDown)
        left  = sib (subtract 1) (^?_head) True <$> tagPromptlyDyn treeD (keybind bodyEl ArrowLeft)
        right = sib (+1) (^?_last) True <$> tagPromptlyDyn treeD (keybind bodyEl ArrowRight)
    selection <- fromUpdates Nothing $ [sel, desel] ++ map (fmap (ifN <*>)) [up, down, left, right]

    dragging <- holdDyn Nothing (leftmost [Nothing <$ domEvent Dragend div, Just <$> draggedE])
    let dropsE = attachPromptlyDynWithMaybe (\g r -> (,r) <$> g) dragging droppedE

  return (selection, dropsE)

