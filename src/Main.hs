{-# LANGUAGE TemplateHaskell #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import ProofCas.TermView

example = Infix "=" (Infix "*" (Constant "a") (Constant "x")) (Infix "*" (Constant "b") (Constant "x"))

main :: IO ()
main = mainWidgetWithCss $(embedFile "term.css") $ renderTerm example

