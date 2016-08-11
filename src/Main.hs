{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Morte.Core
import Morte.Parser
import Text.Read
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import Control.Applicative (liftA2)
import Control.Monad
import Control.Monad.Trans
import GHCJS.DOM.Document
import ProofCas.Pretty
import ProofCas.ExprView

deriving instance Read Const
deriving instance Read Var
deriving instance Read a => Read (Expr a)
instance Read X where
  readsPrec _ _ = []

clearEmbeds :: Expr Path -> Maybe (Expr X)
clearEmbeds = traverse (const Nothing)

fromCode bodyEl c = case clearEmbeds <$> exprFromText (TL.pack (T.unpack c)) of
  Left err          -> text (T.pack (show err))
  Right Nothing     -> text "You can't import stuff here."
  Right (Just expr) -> exprWidget expr bodyEl

fromCode' bodyEl c = case readMaybe (T.unpack c) of
  Nothing   -> text "No read."
  Just expr -> exprWidget expr bodyEl

main :: IO ()
main = mainWidgetWithCss $(embedFile "expr.css") $ do
  ti <- textInput def
  let newCode = tagPromptlyDyn (value ti) (textInputGetEnter ti)
  document <- Control.Monad.Trans.lift askDocument
  Just rawBody <- getBody document
  bodyEl <- wrapRawElement rawBody def
  widgetHold (return ()) $ fromCode' bodyEl <$> newCode
  return ()

