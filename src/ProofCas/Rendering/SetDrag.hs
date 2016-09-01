{-# LANGUAGE CPP #-}
module ProofCas.Rendering.SetDrag where

import GHCJS.DOM.EventM (EventM, event)
import GHCJS.DOM.Types (IsMouseEvent)
#ifdef __GHCJS__
import GHCJS.DOM.MouseEvent (getDataTransfer)
import GHCJS.DOM.DataTransfer
#endif

setCurrentDragData :: IsMouseEvent e => String -> String -> EventM t e ()
#ifdef __GHCJS__
setCurrentDragData k v = do
  e <- event
  Just dt <- getDataTransfer e
  setData dt k v
#else
setCurrentDragData _ _ = return ()
#endif

