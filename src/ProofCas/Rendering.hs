{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module ProofCas.Rendering where

import Reflex.Dom
import GHCJS.DOM.EventM (EventM)
import GHCJS.DOM.Types (IsElement, IsEvent)
import Control.Lens
import Control.Lens.Internal.Context (sell)
import Control.Monad.Reader
import Control.Applicative
import Data.List
import qualified Data.Map as M
import qualified Data.List.NonEmpty as N
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import Data.String
import Data.Proxy
import ProofCas.Rendering.SetDrag
import ProofCas.Navigation

type P id = (StPart, id)

data RenderRes t id =
  RenderRes {
    termClicks :: [Event t (P id)],
    termHovs   :: [Event t (P id)],
    termDhvs   :: [Event t (P id)],
    termDrags  :: [Event t (P id)],
    termDrops  :: [Event t (P id)],
    tree       :: Tree StPart id
  }

instance Ord id => Monoid (RenderRes t id) where
  mempty = RenderRes mempty mempty mempty mempty mempty mempty
  mappend (RenderRes tc th tv td td_ t) (RenderRes tc' th' tv' td' td_' t') =
    RenderRes (tc <> tc') (th <> th') (tv <> tv') (td <> td') (td_ <> td_') (t <> t')

data RenderCtx t id =
  RenderCtx {
    selection :: Demux t (Maybe (P id)),
    hover     :: Demux t (Maybe (P id)),
    dragHover :: Demux t (Maybe (P id))
  }

type RenderM t id m = ReaderT (RenderCtx t id) m
type Render  t id m = RenderM t id m (RenderRes t id)

renderRes ::
  Reflex t => P id -> Event t a -> Event t b -> Event t c -> Event t d -> Event t e -> RenderRes t id
renderRes stid clickE hovE dhvE dragE dropE =
  RenderRes [stid <$ clickE] [stid <$ hovE] [stid <$ dhvE] [stid <$ dragE] [stid <$ dropE] M.empty

execRender :: Monad m => RenderCtx t id -> Render t id m -> m (RenderRes t id)
execRender ctx = flip runReaderT ctx

evOpt :: forall m en er t.
  (DomSpace (DomBuilderSpace m)) =>
  EventName en -> EventFlags ->
  ElementConfig er t m -> ElementConfig er t m
evOpt en ef = elementConfig_eventSpec %~ addEventSpecFlags (Proxy @ (DomBuilderSpace m)) en (const ef)

cn ~^ en = evOpt en stopPropagation cn
cn ~- en = evOpt en preventDefault cn

classesFor ::
  Reflex t => M.Map T.Text (Dynamic t Bool) -> Dynamic t T.Text
classesFor =
  fmap (T.unwords . map fst . filter snd . M.assocs) . sequenceA

addClasses ::
  Reflex t =>
  Dynamic t T.Text -> Dynamic t (M.Map T.Text T.Text) ->
  Dynamic t (M.Map T.Text T.Text)
addClasses = zipDynWith (flip M.alter "class" . alterer)
  where alterer "" a        = a
        alterer c  Nothing  = Just c
        alterer c  (Just a) = Just (a <> " " <> c)

termSpan :: forall t id m.
  (Reflex t, Ord id, MonadWidget t m) => P id -> T.Text -> Render t id m -> Render t id m
termSpan stid termType contents = do
  ctx <- ask
  rec
    let states = [("mouseover", hover), ("dragenter", dragHover), ("selected", selection)]
        statesDyn = foldMap (\(c, f) -> ("term-" <> c) =: demuxed (f ctx) (Just stid)) states

        plainAttrs = constDyn $ "draggable" =: "true" <> "class" =: termType
        attrs      = addClasses (classesFor statesDyn) plainAttrs

        conf = def ~^ Drop ~- Dragover ~^ Dragstart ~^ Click ~^ Mouseover ~^ Dragover

    modifyAttrs <- dynamicAttributesToModifyAttributes attrs
    let conf' = conf & modifyAttributes .~ fmap mapKeysToAttributeName modifyAttrs

    (span, res) <- Reflex.Dom.element "span" conf' contents

  dragE <- wrapDomEvent (_element_raw span) (onEventName Dragstart)
    (setCurrentDragData "dummy" "dummy")
  let ev :: EventName et -> Event t ()
      ev en = void (domEvent en span)
  return $ res <> renderRes stid (ev Click) (ev Mouseover) (ev Dragover) dragE (ev Drop)

textSpan :: MonadWidget t m => T.Text -> m ()
textSpan = elClass "span" "text" . text

bracket :: MonadWidget t m => T.Text -> T.Text -> m a -> m a
bracket o c m = textSpan o *> m <* textSpan c


data RenderItem a =
  Text T.Text | El T.Text (RenderLayer a) | Rec a
  deriving (Functor, Foldable, Traversable)
newtype RenderLayer a = RenderLayer {runRL :: [RenderItem a]}
  deriving (Functor, Foldable, Traversable, Monoid)

instance IsString (RenderLayer a) where
  fromString s = RenderLayer [Text (T.pack s)]

rlel :: T.Text -> RenderLayer a -> RenderLayer a
rlel y = RenderLayer . pure . El y

rlrec :: a -> RenderLayer a
rlrec = RenderLayer . pure . Rec

sepBy :: Monoid m => m -> [m] -> m
sepBy sep = mconcat . intersperse sep

renderLayer :: (MonadWidget t m, Monoid w) => RenderLayer (m w) -> m w
renderLayer = fmap mconcat . traverse renderItem . runRL
  where renderItem (Text t) = mempty <$ textSpan t
        renderItem (El y c) = el y $ renderLayer c
        renderItem (Rec r)  = r


data DTerm id =
  DTerm {
    termType :: T.Text,
    termId :: id,
    parenthesize :: Bool,
    content :: RenderLayer (DTerm id)
  }

renderTerm ::
  (Ord id, MonadWidget t m) =>
  StPart -> DTerm id -> Render t id m
renderTerm part = go Nothing
  where
    go parent dt = (if parenthesize dt then bracket "(" ")" else id) $ do
      let me = termId dt
          (children, cn') = traverse (\subterm -> ([termId subterm], go (Just me) subterm)) (content dt)
      res <- termSpan (part, me) (termType dt) (renderLayer cn')
      return $ res <> mempty{tree=(part, me) =: (parent, children)}


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

proofCasWidget ::
  (Ord id, MonadWidget t m, IsElement (RawElement d)) =>
  Dynamic t (DStatus (DTerm id)) ->
  Element EventResult d t ->
  Event t (N.NonEmpty String) ->
  m (Dynamic t (Maybe (P id)), Event t (P id, P id))
proofCasWidget dstDyn bodyEl errE = do
  rec
    errors <- foldDyn (++) [] (map T.pack . N.toList <$> errE)
    let ctx = RenderCtx (demux selection) (demux hover) (demux dragHover)
    (div, termEvsE) <- elClass' "div" "cas" $ do
      termEvsE <- dyn . ffor dstDyn $ \st -> execRender ctx $ do
        ress <- elClass "div" "assms" $ el "ul" $ do
          forM (_dstatusContext st) $ \(v, dt) -> el "li" $ do
            textSpan $ T.pack v <> " : "
            renderTerm (Assm v) dt
        el "hr" $ return ()
        res' <- elClass "div" "thm" $
          renderTerm Thm (_dstatusTheorem st)
        return $ mconcat ress <> res'
      el "hr" $ return ()
      elClass "div" "errors" $ el "ul" $ do
        dyn . ffor errors $ \es -> do
          forM_ es $ elClass "li" "error" . textSpan
      return termEvsE

    let termEvE which = switchPromptly never $ leftmost . which <$> termEvsE
        clickedW = domEvent Click bodyEl
        hovW     = domEvent Mouseover bodyEl
        dhvW     = domEvent Dragenter bodyEl
    clickedE <- termEvE termClicks
    hovE     <- termEvE termHovs
    dhvE     <- termEvE termDhvs
    draggedE <- termEvE termDrags
    droppedE <- termEvE termDrops
    treeD    <- holdDyn M.empty (tree <$> termEvsE)

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        hov   = const . Just <$> hovE
        dehov = const Nothing <$ hovW
        dhv   = const . Just <$> dhvE
        dedhv = leftmost [const Nothing <$ dhvW, const Nothing <$ dropsE]
        up    = (upwards,   ArrowUp)
        down  = (firstborn, ArrowDown)
        left  = (prevLeaf,  ArrowLeft)
        right = (nextLeaf,  ArrowRight)
        dir (m, e) = runMovement m <$> tagPromptlyDyn treeD (keybind bodyEl e)
    selection <- fromUpdates Nothing $ [sel, desel] ++ map dir [up, down, left, right]
    hover     <- fromUpdates Nothing $ [hov, dehov]
    dragHover <- fromUpdates Nothing $ [dhv, dedhv]

    dragging <- holdDyn Nothing (leftmost [Nothing <$ domEvent Dragend div, Just <$> draggedE])
    let dropsE = attachPromptlyDynWithMaybe (\g r -> (,r) <$> g) dragging droppedE

  return (selection, dropsE)

