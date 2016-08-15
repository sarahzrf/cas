{-# LANGUAGE RecursiveDo #-}
module ProofCas.Interface where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement)
import Morte.Core
import Control.Lens
import Control.Monad
import qualified Data.Text.Lazy as TL
import Data.Monoid
import ProofCas.Proofs
import ProofCas.Contexts
import ProofCas.Paths
import ProofCas.Pretty
import ProofCas.ExprView

fromUpdates :: MonadWidget t m => a -> [Event t (a -> a)] -> m (Dynamic t a)
fromUpdates initial updaters = foldDyn ($) initial (mergeWith (.) updaters)

proofCasWidget ::
  (MonadWidget t m, IsElement (RawElement d)) =>
  Element EventResult d t -> Status -> m ()
proofCasWidget bodyEl initialSt = do
  rec
    let exprEvE which = switchPromptly never $ leftmost . map which <$> exprEvsE
    clickedE <- exprEvE exprClick
    draggedE <- exprEvE exprDrag
    droppedE <- exprEvE exprDrop
    clickedW <- ownEvent Click bodyEl
    let keybind k = ffilter (\n -> keyCodeLookup n == k) (domEvent Keydown bodyEl)

    let sel   = const . Just <$> clickedE
        desel = const Nothing <$ clickedW
        up    = fmap (epathPart%~parent) <$ keybind Space
    selection <- fromUpdates Nothing [sel, desel, up]

    dragging <- holdDyn (StPath Thm []) draggedE
    let -- this will break if you drop other random shit from outside... hmm
        drop  = uncurry swap <$> dragging `attachPromptlyDyn` droppedE
        norm  = fmap (\sel -> stpath sel%~normalize) `fmapMaybe` tagPromptlyDyn selection (keybind Equals)
    stDyn <- fromUpdates initialSt [norm, drop]

    let ctx = RenderCtx (demux selection)
    exprEvsE <- el "div" . dyn . ffor stDyn $ \st -> runRender ctx $ do
      let dst = displayStatus st
      forM (dst^.dstatusCtx.numbered) $ \((v, occ), de) -> do
        textSpan $ TL.toStrict v <> " : "
        renderDExpr de
        el "br" $ return ()
      el "hr" $ return ()
      renderDExpr (_dstatusTheorem dst)
  return ()

