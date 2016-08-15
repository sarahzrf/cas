import Control.Monad
import qualified Data.Text.Lazy as TL
import Morte.Parser

main = forever $ do
  code <- TL.pack <$> getLine
  case exprFromText code of
    Left err   -> print err
    Right expr -> print expr

