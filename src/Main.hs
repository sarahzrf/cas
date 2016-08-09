{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Morte.Core
import Morte.Parser
import Text.Read
import Data.Text.Lazy
import Control.Applicative (liftA2)
import ProofCas.Pretty
import ProofCas.ExprView

deriving instance Read Const
deriving instance Read Var
deriving instance Read a => Read (Expr a)
instance Read X where
  readsPrec _ _ = []

example = Lam "i" idft (App (App (Var "i") idft) (Var "i"))
  where idft = Pi "A" (Morte.Core.Const Star) (Pi "_" (Var "A") (Var "A"))

clearEmbeds :: Expr Path -> Maybe (Expr X)
clearEmbeds = traverse (const Nothing)

fromCode c = case clearEmbeds <$> exprFromText (pack c) of
  Left err          -> text (show err)
  Right Nothing     -> text "You can't import stuff here."
  Right (Just expr) -> renderDExpr (displayExpr expr)

fromCode' c = case readMaybe c of
  Nothing   -> text "No read."
  Just expr -> renderDExpr (displayExpr expr)

main :: IO ()
main = mainWidgetWithCss $(embedFile "expr.css") $ do
  ti <- el "div" $ textInput def
  el "div" $ do
    let newCode = tagDyn (value ti) (textInputGetEnter ti)
    widgetHold (return ()) $ fromCode' <$> newCode
  return ()

