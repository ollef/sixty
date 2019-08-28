module Error.Hydrated where

import Protolude

import Data.Text.Prettyprint.Doc as Doc
import Rock

import Error (Error)
import qualified Error
import Query (Query)
import qualified Query
import qualified Span
import qualified Position

data Hydrated = Hydrated
  { _filePath :: FilePath
  , _lineColumn :: !Span.LineColumn
  , _lineText :: !Text
  , _error :: !Error
  } deriving Show

instance Pretty Hydrated where
  pretty h =
    Error.pretty (_filePath h) (_lineColumn h) (_lineText h) (_error h)

fromError :: Error -> Task Query Hydrated
fromError err = do
  (filePath, span) <- fetch $ Query.ErrorSpan err
  text <- fetch $ Query.FileText filePath
  let
    trimmedSpan =
      Span.trim text span
    (lineColumn, lineText) =
      Span.lineColumn trimmedSpan text
  pure Hydrated
    { _filePath = filePath
    , _lineColumn = lineColumn
    , _lineText = lineText
    , _error = err
    }

lineNumber :: Hydrated -> Int
lineNumber err =
  l
  where
    Span.LineColumns (Position.LineColumn l _) _ =
      _lineColumn err
