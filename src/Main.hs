{-# LANGUAGE TemplateHaskell #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Utils.Vars
import DependentImplicit.Core.Parser
import qualified Data.Text as T
import Control.Monad.Trans
import GHCJS.DOM.Document
import ProofCas.Proofs
import ProofCas.Interface

parseAssm code = (\t -> (FreeVar (T.unpack n), t)) <$> parseTerm (T.unpack (T.tail code'))
  where (n, code') = T.breakOn ":" code

parseStatus code = do
  thm:prf:ctx <- let s = T.splitOn "," code
                 in if length s >= 2 then Right s else Left "not enough parts"
  thm' <- parseTerm (T.unpack thm)
  prf' <- parseTerm (T.unpack prf)
  ctx' <- mapM parseAssm ctx
  return (Status [] [] ctx' thm' prf')

fromCode bodyEl c = case parseStatus c of
  Left err -> text (T.pack err)
  Right st -> proofCasWidget bodyEl st


main :: IO ()
main = mainWidgetWithCss $(embedFile "term.css") $ do
  ti <- textInput def
  let newCode = tagPromptlyDyn (value ti) (textInputGetEnter ti)
  document <- Control.Monad.Trans.lift askDocument
  Just rawBody <- getBody document
  bodyEl <- wrapRawElement rawBody def
  widgetHold (return ()) $ fromCode bodyEl <$> newCode
  return ()

