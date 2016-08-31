{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecursiveDo #-}
module ProofCas.Interface where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import Utils.Vars
import Control.Lens
import Control.Monad
import Data.Functor.Foldable
import Data.Functor.Compose
import qualified Data.Text as T
import Data.Monoid
import ProofCas.Status
import ProofCas.Paths
import ProofCas.TermView
import ProofCas.Proofs

data DStatus e =
  DStatus {
    _dstatusContext :: [(String, e)],
    _dstatusTheorem :: e
  }

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


toDStatus :: Status -> DStatus Subterm
toDStatus Status{_statusContext=ctx, _statusTheorem=thm} =
  DStatus (map ctxEntry ctx) (Subterm ([], thm))
  where ctxEntry (FreeVar v, t) = (v, Subterm ([], t))

keybind :: Reflex t => Element EventResult d t -> Key -> Event t Key
keybind bodyEl k = ffilter (==k) (keyCodeLookup <$> domEvent Keydown bodyEl)

fromUpdates :: MonadWidget t m => a -> [Event t (a -> a)] -> m (Dynamic t a)
fromUpdates initial updaters = foldDyn ($) initial (mergeWith (.) updaters)

sfpWidget ::
  (MonadWidget t m, IsElement (RawElement d)) =>
  Element EventResult d t -> Status -> m ()
sfpWidget bodyEl initialSt = do
  rec
    clickedW <- ownEvent Click bodyEl

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        up    = fmap (_2%~parent) <$ keybind bodyEl Space

    let -- this will break if you drop other random shit from outside... hmm
        drop   = uncurry swap <$> dropsE
        norm   = fmap evalAt `fmapMaybe` tagPromptlyDyn selection (keybind bodyEl Equals)
        factor = fmap factorOutSt `fmapMaybe` tagPromptlyDyn selection (keybind bodyEl KeyF)

    stDyn <- fromUpdates initialSt [drop, norm, factor]
    let dstDyn = toDStatus <$> stDyn
    selection <- fromUpdates Nothing [sel, desel, up]
    (clickedE, dropsE) <- proofCasWidget sfpPrec sfpCls sfpStep dstDyn selection
  return ()

