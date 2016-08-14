{-# LANGUAGE CPP #-}
module ProofCas.SetDrag where

import GHCJS.DOM.EventM (EventM, preventDefault, stopPropagation, event)
import GHCJS.DOM.Types (IsMouseEvent, IsElement, IsEvent)
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

