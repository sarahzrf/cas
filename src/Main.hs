{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Morte.Core
import Morte.Context
import Text.Read
import qualified Data.Text as T
import Control.Monad.Trans
import GHCJS.DOM.Document
import ProofCas.Proofs
import ProofCas.Interface

deriving instance Read Const
deriving instance Read Var
deriving instance Read a => Read (Expr a)
deriving instance Read a => Read (Context a)
deriving instance Read Status
instance Read X where
  readsPrec _ _ = []

fromCode bodyEl c = case readMaybe (T.unpack c) of
  Nothing   -> text "No read."
  Just expr -> proofCasWidget bodyEl expr


main :: IO ()
main = mainWidgetWithCss $(embedFile "expr.css") $ do
  ti <- textInput def
  let newCode = tagPromptlyDyn (value ti) (textInputGetEnter ti)
  document <- Control.Monad.Trans.lift askDocument
  Just rawBody <- getBody document
  bodyEl <- wrapRawElement rawBody def
  widgetHold (return ()) $ fromCode bodyEl <$> newCode
  return ()

