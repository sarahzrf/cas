{-# LANGUAGE TemplateHaskell #-}
module ProofCas.Rendering.TH where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Text.Parsec
import Data.Bifunctor
import Data.Text (pack)
import ProofCas.Rendering

type ExpParser = Parsec String () ExpQ

nonspecial :: Parsec String u Char
nonspecial = noneOf specials <|> (char '\\' >> oneOf specials)
  where specials = "\\$<%,"

literal :: ExpParser
literal =  litE . StringL <$> many1 nonspecial

node :: ExpParser
node = do
  nodeType <- try (char '<' >> many1 alphaNum)
  body <- [| mempty |] <$ string "/>" <|>
    char '>' *> layer <* string ("</" ++ nodeType ++ ">")
  return [| rlel nodeType $body |]

splice :: Char -> (ExpQ -> ExpQ) -> ExpParser
splice pre f = char pre >>
  f . varE . mkName <$> many1 (alphaNum <|> char '\'')

laySplice :: ExpParser
laySplice = splice ',' id

strSplice :: ExpParser
strSplice = splice '$' (appE [| fromString |])

recSplice :: ExpParser
recSplice = splice '%' (appE [| rlrec |])

layer :: ExpParser
layer = (\parts -> [| mconcat $(listE parts) |]) <$> many part
  where part = literal <|> node <|> laySplice <|> strSplice <|> recSplice

parseRL :: String -> ExpQ
parseRL code = either (fail . show) id $
  parse layer "rl quasiquote" code

rl :: QuasiQuoter
rl = QuasiQuoter {quoteExp = parseRL,
  quotePat = error "no pat", quoteType = error "no type", quoteDec = error "no dec"}

