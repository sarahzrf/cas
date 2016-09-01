{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module ProofCas.Rendering.WriterInstances where

import Reflex.Dom
import Control.Monad.Writer

instance (Monoid w, HasWebView m) => HasWebView (WriterT w m) where
  type WebViewPhantom (WriterT w m) = WebViewPhantom m
  askWebView = lift askWebView

fixECfg   :: ElementConfig er t (WriterT w m) -> ElementConfig er t m
fixPCfg   :: (Reflex t, Functor m) => PlaceholderConfig er t (WriterT w m) -> PlaceholderConfig er t m
fixIECfg  :: InputElementConfig er t (WriterT w m) -> InputElementConfig er t m
fixTAECfg :: TextAreaElementConfig er t (WriterT w m) -> TextAreaElementConfig er t m
fixRECfg  :: RawElementConfig er t (WriterT w m) -> RawElementConfig er t m

fixECfg   c = c{_elementConfig_eventSpec=_elementConfig_eventSpec c}
fixPCfg   c = c{_placeholderConfig_insertAbove=fmap fst . runWriterT <$> (_placeholderConfig_insertAbove c)}
fixIECfg  c = c{_inputElementConfig_elementConfig=fixECfg (_inputElementConfig_elementConfig c)}
fixTAECfg c = c{_textAreaElementConfig_elementConfig=fixECfg (_textAreaElementConfig_elementConfig c)}
fixRECfg  c = c{_rawElementConfig_eventSpec=_rawElementConfig_eventSpec c}

instance (DomBuilder t m, Monoid w, MonadHold t m, MonadFix m) => DomBuilder t (WriterT w m) where
  type DomBuilderSpace (WriterT w m) = DomBuilderSpace m
  textNode = liftTextNode
  element elementTag cfg = WriterT . fmap reassoc . element elementTag (fixECfg cfg) . runWriterT
    where reassoc (el, (a, w)) = ((el, a), w)
  placeholder      = lift . placeholder . fixPCfg
  inputElement     = lift . inputElement . fixIECfg
  textAreaElement  = lift . textAreaElement . fixTAECfg
  placeRawElement  = lift . placeRawElement
  wrapRawElement e = lift . wrapRawElement e . fixRECfg

instance (Deletable t m, Reflex t, Monoid w, MonadHold t m, MonadFix m) => Deletable t (WriterT w m) where
  deletable delete = WriterT . deletable delete . runWriterT

instance (Monoid w, PerformEvent t m) => PerformEvent t (WriterT w m) where
  type Performable (WriterT w m) = Performable m
  performEvent_ = lift . performEvent_
  performEvent  = lift . performEvent

instance (Monoid w, TriggerEvent t m) => TriggerEvent t (WriterT w m) where
  newTriggerEvent = lift newTriggerEvent
  newTriggerEventWithOnComplete = lift newTriggerEventWithOnComplete
  newEventWithLazyTriggerWithOnComplete = lift . newEventWithLazyTriggerWithOnComplete

instance (Monoid w, PostBuild t m) => PostBuild t (WriterT w m) where
  getPostBuild = lift getPostBuild

instance (Monoid w, HasJS x m) => HasJS x (WriterT w m) where
  type JSM (WriterT w m) = JSM m
  liftJS = lift . liftJS

