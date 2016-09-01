{-# LANGUAGE RecursiveDo #-}
module ProofCas.Backends.SFP.Interface where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement, IsEvent)
import Utils.Vars
import Control.Lens
import ProofCas.Rendering
import ProofCas.Backends.SFP.Rendering
import ProofCas.Backends.SFP.Status
import ProofCas.Backends.SFP.Paths
import ProofCas.Backends.SFP.Proofs

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

