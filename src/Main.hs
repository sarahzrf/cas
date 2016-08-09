{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Morte.Core
import ProofCas.ExprView

example = Lam "i" idft (App (App (Var "i") idft) (Var "i"))
  where idft = Pi "A" (Morte.Core.Const Star) (Pi "_" (Var "A") (Var "A"))

main :: IO ()
main = mainWidgetWithCss $(embedFile "expr.css") $ renderExpr example

