{-# language FlexibleContexts #-}
{-# language OverloadedStrings #-}
module Error.Hydrated where

import Protolude

import Data.Coerce
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc as Doc
import qualified Data.Text.Unsafe as Text
import Rock

import Error (Error)
import qualified Error
import qualified Error.Parsing
import Name (Name)
import qualified Position
import qualified Pretty
import Query (Query)
import qualified Query
import qualified Scope
import qualified Span

data Hydrated = Hydrated
  { _filePath :: FilePath
  , _lineColumn :: !Span.LineColumn
  , _lineText :: !Text
  , _error :: !Error
  } deriving Show

headingAndBody :: MonadFetch Query m => Error -> m (Doc ann, Doc ann)
headingAndBody error =
  case error of
    Error.Parse _ parse ->
      pure
        ("Parse error"
        , Doc.pretty (Error.Parsing.reason parse) <>
          case Error.Parsing.expected parse of
            [] ->
              mempty

            expected ->
              line <> "Expected: " <> hcat (punctuate comma $ Doc.pretty <$> expected)
        )

    Error.DuplicateName (Scope.KeyedName _ name) ->
      pure
        ( "Duplicate name: " <+> Doc.pretty name
        , Doc.pretty name <+> "has already been defined."
        )

    Error.Elaboration _ (Error.Spanned _ err') ->
      case err' of
        Error.NotInScope name ->
          pure
            ( "Not in scope:" <+> Doc.pretty name
            , Doc.pretty name <+> " is not defined here."
            )

        Error.Ambiguous name constrCandidates nameCandidates ->
          pure
            ("Ambiguous name:" <+> Doc.pretty name
            , "Candidates are:" <+>
              hcat
                (punctuate comma $
                  Doc.pretty <$> toList constrCandidates <|> Doc.pretty <$> toList nameCandidates
                )
            )

        Error.TypeMismatch mismatches -> do
          mismatches' <- forM mismatches $ \(inferred, expected) -> do
            inferred' <- prettyPrettyableTerm inferred
            expected' <- prettyPrettyableTerm expected
            pure (inferred', expected')
          pure
            ( "Type mismatch"
            , vcat
                (intercalate ["", "while trying to unify"]
                  [ [ "Inferred:" <+> inferred
                    , "Expected:" <+> expected
                    ]
                  | (inferred, expected) <- toList mismatches'
                  ]
                )
            )

        Error.OccursCheck mismatches -> do
          mismatches' <- forM mismatches $ \(inferred, expected) -> do
            inferred' <- prettyPrettyableTerm inferred
            expected' <- prettyPrettyableTerm expected
            pure (inferred', expected')
          pure
            ( "Occurs check failed"
            , vcat
                (intercalate ["", "while trying to unify"]
                  [ [ "Inferred:" <+> inferred
                    , "Expected:" <+> expected
                    ]
                  | (inferred, expected) <- toList mismatches'
                  ]
                )
              <> line <> line <>
              "Unifying these values would produce a cyclic term."
            )

        Error.UnsolvedMetaVariable index type_ -> do
          type' <- prettyPrettyableTerm type_
          pure
            ( "Unsolved meta variable"
            , "A meta variable was created here but was never solved:" <> line <> line <>
              Doc.pretty index <+> ":" <+> type'
            )

        Error.NonExhaustivePatterns ->
          pure ("Non-exhaustive patterns", mempty)

        Error.RedundantMatch matchKind ->
          pure ("Redundant" <+> Doc.pretty matchKind, "This" <+> Doc.pretty matchKind <+> "is unreachable")

        Error.PlicityMismatch fieldOrArg plicityMismatch ->
          pure $ case plicityMismatch of
            Error.Mismatch expected_ actual ->
              ( "Plicity mismatch"
              , "Expected an" <+> Doc.pretty expected_ <+> Doc.pretty fieldOrArg <+>
                "but got an" <+> Doc.pretty actual <+> Doc.pretty fieldOrArg
              )

            Error.Missing expected_ ->
              ( "Missing" <+> Doc.pretty fieldOrArg
              , "Expected an" <+> Doc.pretty expected_ <+> Doc.pretty fieldOrArg <+>
                "but didn't get any"
              )

            Error.Extra ->
              ( "Unexpected" <+> Doc.pretty fieldOrArg
              , "Didn't expect a" <+> Doc.pretty fieldOrArg <+> "here"
              )

        Error.UnableToInferImplicitLambda ->
          pure ("Unable to infer implicit lambda", mempty)

        Error.ImplicitApplicationMismatch names term type_ -> do
          term' <- prettyPrettyableTerm term
          type' <- prettyPrettyableTerm type_
          pure
            ( "Plicity mismatch"
            , "The term" <> line <> line <>
              indent 4 term' <> line <> line <>
              "doesn't accept implicit arguments named" <> line <> line <>
              indent 4 (hcat $ punctuate comma $ Doc.pretty <$> toList names) <> line <> line <>
              "Its type is:" <> line <> line <> type'
            )

pretty :: MonadFetch Query m => Hydrated -> m (Doc ann)
pretty h = do
  (heading, body) <- headingAndBody $ _error h
  pure $
    Doc.pretty (_filePath h) <> ":" <> Doc.pretty (_lineColumn h) <> ":" <+> heading <> line <> line <>
    body <> line <> line <>
    spannedLine
  where
    spannedLine =
      let
        Span.LineColumns
          (Position.LineColumn startLineNumber startColumnNumber)
          (Position.LineColumn endLineNumber endColumnNumber) =
            _lineColumn h

        lineNumberText =
          show (startLineNumber + 1)

        lineNumberTextLength =
          Text.lengthWord16 lineNumberText

        (spanLength, spanEnding)
          | startLineNumber == endLineNumber =
            (endColumnNumber - startColumnNumber, mempty)
          | otherwise =
            (Text.lengthWord16 (_lineText h) - startColumnNumber, "...")
      in
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <> line <>
      Doc.pretty lineNumberText <> " | " <> Doc.pretty (_lineText h) <> line <>
      Doc.pretty (Text.replicate (lineNumberTextLength + 1) " ") <> "| " <>
      Doc.pretty (Text.replicate startColumnNumber " " <> "^" <> Text.replicate (spanLength - 1) "~" <> spanEnding)

fromError :: Error -> Task Query Hydrated
fromError err = do
  (filePath, span) <-
    case err of
      Error.Parse filePath parseError ->
        pure
          ( filePath
          , Span.Absolute (Error.Parsing.position parseError) (Error.Parsing.position parseError)
          )

      Error.DuplicateName keyedName ->
        fetch $ Query.KeyedNameSpan keyedName

      Error.Elaboration keyedName (Error.Spanned relativeSpan _) -> do
        (file, Span.Absolute absolutePosition _) <- fetch $ Query.KeyedNameSpan keyedName
        pure (file, Span.absoluteFrom absolutePosition relativeSpan)
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

-------------------------------------------------------------------------------

lineNumber :: Hydrated -> Int
lineNumber err =
  l
  where
    Span.LineColumns (Position.LineColumn l _) _ =
      _lineColumn err

prettyPrettyableTerm :: MonadFetch Query m => Error.PrettyableTerm -> m (Doc ann)
prettyPrettyableTerm (Error.PrettyableTerm moduleName_ names term) = do
  env <- Pretty.emptyM moduleName_
  pure $ go names env
  where
    go :: [Name] -> Pretty.Environment v -> Doc ann
    go names' env' =
      case names' of
        [] ->
          Pretty.prettyTerm 0 (coerce env') term

        name:names'' ->
          let
            (env'', _) = Pretty.extend env' name

          in
          go names'' env''
