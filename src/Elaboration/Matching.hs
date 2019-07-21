{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module Elaboration.Matching where

import Protolude hiding (force)

import Control.Monad.Fail
import Control.Monad.Trans.Maybe
import qualified Data.HashSet as HashSet
import Data.Vector (Vector)
import Rock

import {-# source #-} qualified Elaboration
import qualified Builtin
import Context (Context)
import qualified Context
import Data.Some (Some(Some))
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Domain.Telescope as Domain (Telescope)
import qualified Domain.Telescope
import qualified Evaluation
import Monad
import Name (Name(Name))
import qualified Name
import Plicity
import qualified Presyntax
import qualified Query
import qualified Readback
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import qualified Unification
import Var

data Config = Config
  { _targetType :: !Domain.Value
  , _scrutinees :: !(Vector Domain.Value)
  , _clauses :: [Clause]
  }

data Clause = Clause
  { _matches :: [Match]
  , _rhs :: !Presyntax.Term
  }

data Match = Match !Domain.Value !Plicity !Presyntax.Pattern !Domain.Type

-------------------------------------------------------------------------------

elaborateCase
  :: Context v
  -> Syntax.Term v
  -> Domain.Type
  -> [(Presyntax.Pattern, Presyntax.Term)]
  -> Domain.Type
  -> M (Syntax.Term v)
elaborateCase context scrutinee scrutineeType branches expectedType =
  case scrutinee of
    Syntax.Var index -> do
      let
        scrutineeValue =
          Domain.var $ Context.lookupIndexVar index context
      -- TODO coverage check
      elaborate context Config
        { _targetType = expectedType
        , _scrutinees = pure scrutineeValue
        , _clauses =
          [ Clause
            { _matches = [Match scrutineeValue Explicit pattern scrutineeType]
            , _rhs = rhs'
            }
          | (pattern, rhs') <- branches
          ]
        }

    _ -> do
      (context', var) <- Context.extend context "scrutinee" $ Lazy $ pure scrutineeType
      let
        index =
          Context.lookupVarIndex var context'
      term <- elaborateCase context' (Syntax.Var index) scrutineeType branches expectedType
      scrutineeType' <- Readback.readback (Context.toReadbackEnvironment context) scrutineeType
      pure $ Syntax.Let "scrutinee" scrutineeType' scrutinee term

-------------------------------------------------------------------------------

elaborate :: Context v -> Config -> M (Syntax.Term v)
elaborate context config = do
  clauses <- catMaybes <$> mapM (simplifyClause context) (_clauses config)
  let
    config' = config { _clauses = clauses }
  case clauses of
    [] ->
      panic "TODO uninhabitation check"

    firstClause:_ -> do
      let
        matches = _matches firstClause
      maybeConMatch <- findConMatches context matches
      case maybeConMatch of
        Just (var, span, constr, typ) ->
          splitConstructor context config' var span constr typ

        Nothing -> do
          maybeSub <- solved context matches
          case maybeSub of
            Nothing ->
              panic "matching: no solution"

            Just sub -> do
              Some context' <- Context.extendDefs context sub
              mapM_ (checkForcedPattern context') matches
              result <- Elaboration.check context' (_rhs firstClause) (_targetType config)
              -- TODO escape check instead of coercion?
              pure $ Syntax.coerce result

checkForcedPattern :: Context v -> Match -> M ()
checkForcedPattern context match =
  case match of
    Match value1 _ (Presyntax.Pattern span (Presyntax.Forced term)) type_ -> do
      let
        context' =
          Context.spanned span context

      term' <- Elaboration.check context' term type_
      value2 <- Elaboration.evaluate context term'
      -- TODO recover from failure
      Unification.unify context' value1 value2

    _ ->
      pure ()

-------------------------------------------------------------------------------

simplifyClause :: Context v -> Clause -> M (Maybe Clause)
simplifyClause context clause = do
  maybeMatches <- runMaybeT $
    concat <$> mapM (simplifyMatch context) (_matches clause)
  case maybeMatches of
    Nothing ->
      return Nothing

    Just matches' -> do
      maybeExpanded <- runMaybeT $ expandAnnotations context matches'
      case maybeExpanded of
        Nothing ->
          pure $ Just clause { _matches = matches' }

        Just expandedMatches ->
          simplifyClause context clause { _matches = expandedMatches }

simplifyMatch
  :: Context v
  -> Match
  -> MaybeT M [Match]
simplifyMatch context (Match value plicity pattern@(Presyntax.Pattern span unspannedPattern) type_) = do
  value' <- lift $ Context.forceHead context value
  let
    match' =
      Match value' plicity pattern type_
  case (value', unspannedPattern) of
    (Domain.Neutral (Domain.Con constr) spine, Presyntax.ConOrVar name pats) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) name
      case maybeScopeEntry of
        Just (Scope.Constructors constrs)
          | constr `HashSet.member` constrs ->
            lift $ do
              constrType <- fetch $ Query.ConstructorType constr
              (patsType, patSpine) <-
                instantiateConstructorType
                  (Context.toEvaluationEnvironment context)
                  (Telescope.fromVoid constrType)
                  (toList spine)

              (matches', type') <- matchPrepatterns patSpine pats patsType
              -- TODO: Recover from failure
              Unification.unify (Context.spanned span context) type_ type'
              pure matches'

          | otherwise ->
            fail "Constructor mismatch"

        _ ->
          pure [match']

    _ ->
      pure [match']

instantiateConstructorType
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.Type v
  -> [(Plicity, Lazy Domain.Value)]
  -> M (Domain.Type, [(Plicity, Lazy Domain.Value)])
instantiateConstructorType env tele spine =
  case (tele, spine) of
    (Telescope.Empty constrType, _) -> do
      constrType' <- Evaluation.evaluate env constrType
      pure (constrType', spine)

    (Telescope.Extend _ _ _ tele', (Implicit, arg):spine') -> do
      env' <- Domain.extendValue env arg
      instantiateConstructorType env' tele' spine'

    _ ->
      panic "TODO match tele error message"

-- TODO: handle implicits that haven't been given
matchPrepatterns
  :: [(Plicity, Lazy Domain.Value)]
  -> [(Plicity, Presyntax.Pattern)]
  -> Domain.Type
  -> M ([Match], Domain.Type)
matchPrepatterns values patterns type_ =
  case (values, patterns) of
    ([], []) ->
      pure ([], type_)

    ((plicity1, value):values', (plicity2, pattern):patterns')
      | plicity1 == plicity2
      , Domain.Pi _ source plicity3 domainClosure <- type_
      , plicity2 == plicity3 -> do
        domain <- Evaluation.evaluateClosure domainClosure value
        (matches, type') <- matchPrepatterns values' patterns' domain
        value' <- force value
        source' <- force source
        pure (Match value' plicity1 pattern source' : matches, type')

      | plicity1 == Explicit
      , plicity2 == Explicit
      , Domain.Fun source domain <- type_ -> do
        domain' <- force domain
        (matches, type') <- matchPrepatterns values' patterns' domain'
        value' <- force value
        source' <- force source
        pure (Match value' Explicit pattern source' : matches, type')

    _ ->
      panic "matchPrepatterns TODO error message"

type PatternSubstitution = Tsil (Name, Lazy Domain.Value, Lazy Domain.Value)

expandAnnotations
  :: Context v
  -> [Match]
  -> MaybeT M [Match]
expandAnnotations context matches =
  case matches of
    [] ->
      fail "expanded nothing"

    match:matches' -> do
      maybeSub <- lift $ runMaybeT $ matchSubstitution context match
      case maybeSub of
        Just sub -> do
          Some context' <- lift $ Context.extendDefs context sub
          matches'' <- expandAnnotations context' matches'
          pure $ match : matches''

        Nothing ->
          case match of
            Match term plicity (Presyntax.Pattern span (Presyntax.Anno pat annoType)) type_ -> do
              lift $ do
                annoType' <- Elaboration.check context annoType Builtin.type_
                -- TODO: Recover from failure
                annoType'' <- Elaboration.evaluate context annoType'
                Unification.unify (Context.spanned span context) annoType'' type_
              pure $ Match term plicity pat type_ : matches'

            _ ->
              fail "couldn't create substitution for prefix"

matchSubstitution :: Context v -> Match -> MaybeT M PatternSubstitution
matchSubstitution context match =
  case match of
    (Match _ _ (Presyntax.Pattern _ Presyntax.WildcardPattern) _) ->
      pure mempty

    (Match term _ (Presyntax.Pattern _ (Presyntax.ConOrVar prename@(Name.Pre name) [])) type_) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
      case maybeScopeEntry of
        Just (Scope.Constructors _) ->
          fail "No match substitution"

        _ ->
          pure $ pure (Name name, Lazy $ pure term, Lazy $ pure type_)

    (Match _ _ (Presyntax.Pattern _ (Presyntax.Forced _)) _) ->
      pure mempty

    _ ->
      fail "No match substitution"

solved :: Context v -> [Match] -> M (Maybe PatternSubstitution)
solved context =
  runMaybeT . fmap mconcat . traverse (matchSubstitution context)

-------------------------------------------------------------------------------

findConMatches
  :: Context v
  -> [Match]
  -> M (Maybe (Var, Span.Relative, Name.QualifiedConstructor, Domain.Type))
findConMatches context matches =
    case matches of
      [] ->
        pure Nothing

      Match (Domain.Neutral (Domain.Var x) Tsil.Empty) _ (Presyntax.Pattern span (Presyntax.ConOrVar name _)) type_:matches' -> do
        maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) name
        case maybeScopeEntry of
          Just (Scope.Constructors constrs) -> do
            expectedTypeName <- lazy $ Elaboration.getExpectedTypeName context type_
            maybeConstr <- Elaboration.resolveConstructor context name constrs expectedTypeName
            case maybeConstr of
              Nothing ->
                findConMatches context matches'

              Just constr ->
                pure $ Just (x, span, constr, type_)

          -- TODO ambiguity errors?
          _ ->
            findConMatches context matches'

      _:matches' ->
        findConMatches context matches'

splitConstructor
  :: Context v
  -> Config
  -> Var
  -> Span.Relative
  -> Name.QualifiedConstructor
  -> Domain.Type
  -> M (Syntax.Type v)
splitConstructor outerContext config scrutinee span (Name.QualifiedConstructor typeName _) outerType = do
  let
    goParams
      :: Context v
      -> Domain.Spine
      -> Domain.Telescope Domain.Type [(Name.Constructor, Domain.Type)]
      -> M (Syntax.Type v)
    goParams context conArgs dataTele =
      case dataTele of
        Domain.Telescope.Empty constructors -> do
          branches <- forM constructors $ \(constr, constrType) -> do
            let
              qualifiedConstr =
                Name.QualifiedConstructor typeName constr
            branchTele <- goConstrFields context qualifiedConstr conArgs constrType
            pure $ Syntax.Branch qualifiedConstr branchTele
          pure $ Syntax.Case (Syntax.Var $ Context.lookupVarIndex scrutinee context) branches

        Domain.Telescope.Extend _ source plicity domainClosure -> do
          param <- lazy $ Context.newMeta source context
          domain <- domainClosure param
          goParams context (conArgs Tsil.:> (implicitise plicity, param)) domain

    goConstrFields
      :: Context v
      -> Name.QualifiedConstructor
      -> Domain.Spine
      -> Domain.Type
      -> M (Telescope Syntax.Type Syntax.Term v)
    goConstrFields context constr conArgs type_ =
      case type_ of
        Domain.Pi name source plicity domainClosure -> do
          source' <- force source
          source'' <- Elaboration.readback context source'
          (context' , fieldVar) <- Context.extendBefore context scrutinee name source
          let
            fieldValue =
              Lazy $ pure $ Domain.var fieldVar

            conArgs' =
              conArgs Tsil.:> (plicity, fieldValue)

          domain <- Evaluation.evaluateClosure domainClosure fieldValue
          tele <- goConstrFields context' constr conArgs' domain
          pure $ Telescope.Extend name source'' plicity tele

        Domain.Fun source domain -> do
          source' <- force source
          source'' <- Elaboration.readback context source'
          (context' , fieldVar) <- Context.extendBefore context scrutinee "x" source
          let
            fieldValue =
              Lazy $ pure $ Domain.var fieldVar

            conArgs' =
              conArgs Tsil.:> (Explicit, fieldValue)

          domain' <- force domain
          tele <- goConstrFields context' constr conArgs' domain'
          pure $ Telescope.Extend "x" source'' Explicit tele

        _ -> do
          let
            context' =
              Context.define context scrutinee $ Lazy $ pure $ Domain.Neutral (Domain.Con constr) conArgs
          -- TODO recover from failure
          Unification.unify context' type_ outerType
          result <- elaborate context' config
          pure $ Telescope.Empty result

  maybeDefinition <- fetch $ Query.ElaboratedDefinition typeName
  case maybeDefinition of
    Just (Syntax.DataDefinition tele, _) -> do
      tele' <- Evaluation.evaluateConstructorDefinitions (Domain.empty $ Context.scopeKey outerContext) tele
      goParams (Context.spanned span outerContext) mempty tele'

    _ ->
      panic "splitConstructor no data definition"
