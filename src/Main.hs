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
import ProofCas.Pretty
import ProofCas.ExprView

deriving instance Read Const
deriving instance Read Var
deriving instance Read a => Read (Expr a)
instance Read X where
  readsPrec _ _ = []

clearEmbeds :: Expr Path -> Maybe (Expr X)
clearEmbeds = traverse (const Nothing)

fromCode c = case clearEmbeds <$> exprFromText (TL.pack (T.unpack c)) of
  Left err          -> text (T.pack (show err))
  Right Nothing     -> text "You can't import stuff here."
  Right (Just expr) -> exprWidget expr

fromCode' c = case readMaybe (T.unpack c) of
  Nothing   -> text "No read."
  Just expr -> exprWidget expr

main :: IO ()
main = mainWidgetWithCss $(embedFile "expr.css") $ do
  ti <- el "div" $ textInput def
  let newCode = tagPromptlyDyn (value ti) (textInputGetEnter ti)
  widgetHold (return ()) $ fromCode' <$> newCode
  return ()

