{-# LANGUAGE RecursiveDo #-}
module ProofCas.Backends.SFP.Interface where

import Reflex.Dom
import GHCJS.DOM.Types (IsElement, IsEvent)
import Utils.Vars
import Dependent.Core.Term
import Control.Lens
import qualified Data.List.NonEmpty as N
import ProofCas.Rendering
import ProofCas.Backends.SFP.Rendering
import ProofCas.Backends.SFP.Status
import ProofCas.Backends.SFP.Paths
import ProofCas.Backends.SFP.Proofs

data History a = History {_past :: [a], _present :: a, _future :: [a]}

dawn :: a -> History a
dawn r = History [] r []

back, forth :: History a -> History a
back (History (p:ps) r f) = History ps p (r:f)
back h = h
forth (History p r (f:fs)) = History (r:p) f fs
forth h = h

-- not actually a lens, but the type is right
tomorrow :: Lens' (History a) a
tomorrow m (History p r f) = (\r' -> History (r:p) r' []) <$> m r


toDStatus :: Status -> DStatus Term
toDStatus Status{_statusContext=ctx, _statusTheorem=thm} =
  DStatus (map ctxEntry ctx) thm
  where ctxEntry (FreeVar v, t) = (v, t)

fromUpdatesErr :: MonadWidget t m => a -> [Event t (a -> Either e a)] -> m (Dynamic t a, Event t (N.NonEmpty e))
fromUpdatesErr initial updaters = do
    let l f (a, es) = either (\e -> (a, e:es)) (\a' -> (a', es)) (f a)
        updaters' = mergeWith (.) . map (fmap l) $ updaters
    (val, errs) <- mapAccum (\a f -> f (a, [])) initial updaters'
    return (val, fmapMaybe N.nonEmpty errs)

sfpWidget ::
  (MonadWidget t m, IsElement (RawElement d)) =>
  Element EventResult d t -> Status -> m ()
sfpWidget bodyEl initialSt = do
  rec
    let -- this will break if you drop other random shit from outside... hmm
        drop   = uncurry handleDrop <$> dropsE
        norm   = fmap evalAt `fmapMaybe` tagPromptlyDyn selection (keybind bodyEl Equals)
        factor = fmap factorOutSt `fmapMaybe` tagPromptlyDyn selection (keybind bodyEl KeyF)
        undo   = back  <$ keybind bodyEl KeyU
        redo   = forth <$ keybind bodyEl KeyR
        stUpdaters = map (fmap (tomorrow . proofStep)) [drop, norm, factor]
        hUpdaters  = map (fmap (Right .)) [undo, redo]

    (stHist, errE) <- fromUpdatesErr (dawn initialSt) (stUpdaters ++ hUpdaters)
    let dstDyn = fmap (sfpDisplay [] Nothing) . toDStatus .  _present <$> stHist
    (selection, dropsE) <- proofCasWidget dstDyn bodyEl errE
  return ()

