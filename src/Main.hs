{-# LANGUAGE TemplateHaskell #-}
module Main where

import Reflex.Dom
import Data.FileEmbed
import Utils.Vars
import Utils.ABT
import DependentImplicit.Unification.Elaborator
import DependentImplicit.Unification.Elaboration
import DependentImplicit.Core.Term
import DependentImplicit.Core.Parser
import qualified Data.ByteString.Char8 as BS
import qualified Data.Text as T
import Control.Monad.Trans
import Data.List
import GHCJS.DOM.Document
import ProofCas.Proofs
import ProofCas.Interface

Right std = parseProgram (BS.unpack $(embedFile "std.sfp"))
Right (_, ElabState sig defs _ _ _) = runElaborator0 (elabProgram std)

parseAssm code = (\t -> (FreeVar (T.unpack n), t)) <$> parseTerm (T.unpack (T.tail code'))
  where (n, code') = T.breakOn ":" code

freeToDefinedModCtx :: Context -> ABT TermF -> ABT TermF
freeToDefinedModCtx c = freeToDefined d
  where d s
          | FreeVar s `elem` map fst c = Var (Free (FreeVar s))
          | otherwise = In (Defined s)

parseStatus code = do
  thm:prf:ctx <- let s = T.splitOn "," code
                 in if length s >= 2 then Right s else Left "not enough parts"
  ctx' <- mapM parseAssm ctx
  let ctx'' = zipWith ftdmc (inits ctx') ctx'
      ftdmc c (v, t) = (v, freeToDefinedModCtx c t)
  thm' <- freeToDefinedModCtx ctx'' <$> parseTerm (T.unpack thm)
  prf' <- freeToDefinedModCtx ctx'' <$> parseTerm (T.unpack prf)
  return (Status sig defs ctx'' thm' prf')

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

