{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
import Control.Applicative
import qualified Data.Text.Lazy as TL
import Morte.Core
import Morte.Parser
import Morte.Lexer
import Morte.Context

deriving instance Show a => Show (Context a)

data Status =
  Status {
    _statusCtx     :: Context (Expr X),
    _statusTheorem :: Expr X,
    _statusProof   :: Expr X
  } deriving Show

pathErr = ParseError (P 0 0) (Lexing "You can't import stuff here.")

clearEmbeds :: Expr Path -> Either ParseError (Expr X)
clearEmbeds = traverse (const (Left pathErr))

parseAssm code =
  let (n, TL.tail -> code') = TL.breakOn ":" code
  in (n,) <$> (exprFromText code' >>= clearEmbeds)

parseConcl code =
  let (thmCode, TL.tail -> prfCode) = TL.breakOn "," code
  in liftA2 (,) (exprFromText thmCode >>= clearEmbeds) (exprFromText prfCode >>= clearEmbeds)

main = do
  ls <- TL.lines . TL.pack <$> getContents
  let assms = mapM parseAssm (init ls)
      concl = parseConcl (last ls)
  case liftA2 (uncurry . Status . Context) assms concl of
    Left err -> print err
    Right st -> print st

