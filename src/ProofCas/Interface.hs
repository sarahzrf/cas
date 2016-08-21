{-# LANGUAGE RecursiveDo #-}
module ProofCas.Interface where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import Utils.Vars
import DependentImplicit.Core.Term
import Control.Lens
import Control.Monad
import qualified Data.Text as T
import Data.Monoid
import ProofCas.Status
import ProofCas.Paths
import ProofCas.TermView
import ProofCas.Proofs

evalAt :: StPath -> Status -> Status
evalAt sel st = either (const st) id $ st & stpath sel (evalIn st)


fromUpdates :: MonadWidget t m => a -> [Event t (a -> a)] -> m (Dynamic t a)
fromUpdates initial updaters = foldDyn ($) initial (mergeWith (.) updaters)

proofCasWidget ::
  (MonadWidget t m, IsElement (RawElement d)) =>
  Element EventResult d t -> Status -> m ()
proofCasWidget bodyEl initialSt = do
  rec
    let termEvE which = switchPromptly never $ leftmost . map which <$> termEvsE
    clickedE <- termEvE termClick
    draggedE <- termEvE termDrag
    droppedE <- termEvE termDrop
    clickedW <- ownEvent Click bodyEl
    let keybind k = ffilter (\n -> keyCodeLookup n == k) (domEvent Keydown bodyEl)

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        up    = fmap (tpathPart%~parent) <$ keybind Space
    selection <- fromUpdates Nothing [sel, desel, up]

    dragging <- holdDyn (StPath Thm []) draggedE
    let -- this will break if you drop other random shit from outside... hmm
        drop   = uncurry swap <$> dragging `attachPromptlyDyn` droppedE
        norm   = fmap evalAt `fmapMaybe` tagPromptlyDyn selection (keybind Equals)
        factor = fmap factorOutSt `fmapMaybe` tagPromptlyDyn selection (keybind KeyF)
    stDyn <- fromUpdates initialSt [drop, norm, factor]

    let ctx = RenderCtx (demux selection)
    termEvsE <- el "div" . dyn . ffor stDyn $ \st -> runRender ctx $ do
      forM (st^.statusContext) $ \(FreeVar v, de) -> do
        textSpan $ T.pack v <> " : "
        renderTerm de (StPath (Assm v) [])
        el "br" $ return ()
      el "hr" $ return ()
      renderTerm (_statusTheorem st) (StPath Thm [])
  return ()

