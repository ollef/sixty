{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
module Elaboration.Matching where

import Protolude hiding (force)

import Control.Monad.Fail
import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.IORef
import Data.Set (Set)
import qualified Data.Set as Set
import Rock

import {-# source #-} qualified Elaboration
import qualified Builtin
import Context (Context)
import qualified Context
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Domain.Telescope as Domain (Telescope)
import qualified Domain.Telescope
import qualified Error
import qualified Evaluation
import qualified Flexibility
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
import qualified Unification.Indices as Indices
import Var

data Config = Config
  { _expectedType :: !Domain.Value
  , _scrutinees :: ![Domain.Value]
  , _clauses :: [Clause]
  , _usedClauses :: !(IORef (Set Span.Relative))
  }

data Clause = Clause
  { _span :: !Span.Relative
  , _matches :: [Match]
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
      usedClauses <- liftIO $ newIORef mempty

      elaborateWithCoverage context Config
        { _expectedType = expectedType
        , _scrutinees = pure scrutineeValue
        , _clauses =
          [ Clause
            { _span = Span.add patSpan rhsSpan
            , _matches = [Match scrutineeValue Explicit pat scrutineeType]
            , _rhs = rhs'
            }
          | (pat@(Presyntax.Pattern patSpan _), rhs'@(Presyntax.Term rhsSpan _)) <- branches
          ]
        , _usedClauses = usedClauses
        }

    _ -> do
      (context', var) <- Context.extendUnnamed context "scrutinee" $ Lazy $ pure scrutineeType
      let
        index =
          fromMaybe (panic "matching lookupVarIndex") $ Context.lookupVarIndex var context'
      term <- elaborateCase context' (Syntax.Var index) scrutineeType branches expectedType
      scrutineeType' <- Readback.readback (Context.toReadbackEnvironment context) scrutineeType
      pure $ Syntax.Let "scrutinee" scrutinee scrutineeType' term

elaborateClauses
  :: Context v
  -> [Clause]
  -> Domain.Type
  -> M (Syntax.Term v)
elaborateClauses context clauses expectedType = do
  usedClauses <- liftIO $ newIORef mempty

  elaborateWithCoverage context Config
    { _expectedType = expectedType
    , _scrutinees =
      case clauses of
        firstClause:_ ->
          [value | Match value _ _ _ <- _matches firstClause]

        _ ->
          mempty

    , _clauses = clauses
    , _usedClauses = usedClauses
    }

elaborateSingle
  :: Context v
  -> Var
  -> Presyntax.Pattern
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
elaborateSingle context scrutinee pat@(Presyntax.Pattern patSpan _) rhs@(Presyntax.Term rhsSpan _) expectedType = do
    let
      scrutineeValue =
        Domain.var scrutinee
    scrutineeType <- force $ Context.lookupVarType scrutinee context

    usedClauses <- liftIO $ newIORef mempty

    elaborateWithCoverage context Config
      { _expectedType = expectedType
      , _scrutinees = pure scrutineeValue
      , _clauses =
        [ Clause
          { _span = Span.add patSpan rhsSpan
          , _matches = [Match scrutineeValue Explicit pat scrutineeType]
          , _rhs = rhs
          }
        ]
      , _usedClauses = usedClauses
      }

-------------------------------------------------------------------------------

elaborateWithCoverage :: Context v -> Config -> M (Syntax.Term v)
elaborateWithCoverage context config = do
  result <- elaborate context config
  let
    allClauseSpans =
      Set.fromList
        [ span
        | Clause span _ _ <- _clauses config
        ]
  usedClauseSpans <- liftIO $ readIORef (_usedClauses config)
  forM_ (Set.difference allClauseSpans usedClauseSpans) $ \span ->
    Context.report (Context.spanned span context) Error.OverlappingPatterns
  pure result

elaborate :: Context v -> Config -> M (Syntax.Term v)
elaborate context config = do
  clauses <- catMaybes <$> mapM (simplifyClause context) (_clauses config)
  let
    config' = config { _clauses = clauses }
  case clauses of
    [] -> do
      exhaustive <- anyM (uninhabitedScrutinee context) $ _scrutinees config
      unless exhaustive $ Context.report context Error.NonExhaustivePatterns
      targetType <- Elaboration.readback context $ _expectedType config
      pure $ Syntax.App (Syntax.Global Builtin.fail) Explicit targetType

    firstClause:_ -> do
      let
        matches = _matches firstClause

      maybeEqMatch <- findEqualityMatch context matches
      case maybeEqMatch of
        Just (context', var, type_, value1, value2) ->
          splitEquality context' config' var type_ value1 value2

        Nothing -> do
          maybeConMatch <- findConstructorMatch context matches
          case maybeConMatch of
            Just (var, span, constr, type_) ->
              splitConstructor context config' var span constr type_

            Nothing -> do
              maybeInst <- solved context matches
              case maybeInst of
                Nothing ->
                  panic "matching: no solution"

                Just inst -> do
                  context' <- Context.extendUnindexedDefs context inst
                  mapM_ (checkForcedPattern context') matches
                  result <- Elaboration.check context' (_rhs firstClause) (_expectedType config)
                  liftIO $ modifyIORef (_usedClauses config) $ Set.insert $ _span firstClause
                  pure result

checkForcedPattern :: Context v -> Match -> M ()
checkForcedPattern context match =
  case match of
    Match value1 _ (Presyntax.Pattern span (Presyntax.Forced term)) type_ -> do
      let
        context' =
          Context.spanned span context

      term' <- Elaboration.check context' term type_
      value2 <- Elaboration.evaluate context term'
      _ <- Context.try_ context' $ Unification.unify context' Flexibility.Rigid value1 value2
      pure ()

    _ ->
      pure ()

-------------------------------------------------------------------------------

simplifyClause :: Context v -> Clause -> M (Maybe Clause)
simplifyClause context clause = do
  maybeMatches <- runMaybeT $
    concat <$> mapM (simplifyMatch context) (_matches clause)
  case maybeMatches of
    Nothing ->
      pure Nothing

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
simplifyMatch context (Match value plicity pat@(Presyntax.Pattern span unspannedPattern) type_) = do
  value' <- lift $ Context.forceHead context value
  let
    match' =
      Match value' plicity pat type_
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

              (matches', type') <- matchPrepatterns context patSpine pats patsType
              let
                context' =
                  Context.spanned span context
              _ <- Context.try_ context' $ Unification.unify context' Flexibility.Rigid type_ type'
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

    (Telescope.Extend _ _ plicity1 tele', (plicity2, arg):spine')
      | plicity1 == plicity2 -> do
        env' <- Domain.extendValue env arg
        instantiateConstructorType env' tele' spine'

    _ ->
      panic $ "instantiateConstructorType: " <> show (tele, fst <$> spine)

matchPrepatterns
  :: Context v
  -> [(Plicity, Lazy Domain.Value)]
  -> [Presyntax.PlicitPattern]
  -> Domain.Type
  -> M ([Match], Domain.Type)
matchPrepatterns context values patterns type_ = do
  type' <- Context.forceHead context type_
  case (patterns, values, type') of
    ([], [], _) ->
      pure ([], type')

    ( Presyntax.ExplicitPattern pat:patterns'
      , (Explicit, value):values'
      , Domain.Pi _ source Explicit domainClosure
      ) -> do
        domain <- Evaluation.evaluateClosure domainClosure value
        explicitFunCase value values' pat patterns' source domain

    ( Presyntax.ExplicitPattern pat:patterns'
      , (Explicit, value):values'
      , Domain.Fun source domain
      ) -> do
        domain' <- force domain
        explicitFunCase value values' pat patterns' source domain'

    (Presyntax.ExplicitPattern _:_, (Explicit, _):_, _) ->
      panic "matchPrepatterns non-pi"

    (Presyntax.ImplicitPattern _ namedPats:patterns', _, _)
      | HashMap.null namedPats ->
        matchPrepatterns context values patterns' type'

    ( Presyntax.ImplicitPattern patSpan namedPats:patterns'
      , (Implicit, value):values'
      , Domain.Pi name source Implicit domainClosure
      )
      | HashMap.member name namedPats -> do
        domain <- Evaluation.evaluateClosure domainClosure value
        (matches, type'') <-
          matchPrepatterns
            context
            values'
            (Presyntax.ImplicitPattern patSpan (HashMap.delete name namedPats) : patterns')
            domain
        value' <- force value
        source' <- force source
        pure (Match value' Implicit (namedPats HashMap.! name) source' : matches, type'')

    (_, (Implicit, value):values', Domain.Pi _ _ Implicit domainClosure) -> do
      domain <- Evaluation.evaluateClosure domainClosure value
      matchPrepatterns context values' patterns domain

    (_, (Implicit, _):_, _) ->
      panic "matchPrepatterns non-pi"

    (_, (Constraint, value):values', Domain.Pi _ source Constraint domainClosure) -> do
      domain <- Evaluation.evaluateClosure domainClosure value
      (matches, type'') <-
        matchPrepatterns
          context
          values'
          patterns
          domain
      value' <- force value
      source' <- force source
      let
        pattern_ =
          Presyntax.Pattern (Context.span context) Presyntax.WildcardPattern
      pure (Match value' Constraint pattern_ source' : matches, type'')

    (_, (Constraint, _):_, _) ->
      panic "matchPrepatterns non-pi"

    (pat:_, [], _) -> do
      Context.report (Context.spanned (Presyntax.plicitPatternSpan pat) context) $ Error.PlicityMismatch Error.Extra
      pure ([], type')

    ([], (Explicit, _):_, _) -> do
      Context.report context $ Error.PlicityMismatch $ Error.Missing Explicit
      matchPrepatterns context values [Presyntax.ExplicitPattern $ Presyntax.Pattern (Context.span context) Presyntax.WildcardPattern] type'

    (Presyntax.ImplicitPattern patSpan _:patterns', (Explicit, _):_, _) -> do
      Context.report (Context.spanned patSpan context) $ Error.PlicityMismatch (Error.Mismatch Explicit Implicit)
      matchPrepatterns context values patterns' type'
  where
    explicitFunCase value values' pat patterns' source domain = do
      (matches, type'') <- matchPrepatterns context values' patterns' domain
      value' <- force value
      source' <- force source
      pure (Match value' Explicit pat source' : matches, type'')

type PatternInstantiation = Tsil (Name, Lazy Domain.Value, Lazy Domain.Value)

expandAnnotations
  :: Context v
  -> [Match]
  -> MaybeT M [Match]
expandAnnotations context matches =
  case matches of
    [] ->
      fail "expanded nothing"

    match:matches' -> do
      maybeInst <- lift $ runMaybeT $ matchInstantiation context match
      case maybeInst of
        Just inst -> do
          context' <- lift $ Context.extendUnindexedDefs context inst
          matches'' <- expandAnnotations context' matches'
          pure $ match : matches''

        Nothing ->
          case match of
            Match term plicity (Presyntax.Pattern span (Presyntax.Anno pat annoType)) type_ -> do
              lift $ do
                annoType' <- Elaboration.check context annoType Builtin.type_
                annoType'' <- Elaboration.evaluate context annoType'
                let
                  context' =
                    Context.spanned span context
                _ <- Context.try_ context' $ Unification.unify context' Flexibility.Rigid annoType'' type_
                pure ()
              pure $ Match term plicity pat type_ : matches'

            _ ->
              fail "couldn't create instantitation for prefix"

matchInstantiation :: Context v -> Match -> MaybeT M PatternInstantiation
matchInstantiation context match =
  case match of
    (Match _ _ (Presyntax.Pattern _ Presyntax.WildcardPattern) _) ->
      pure mempty

    (Match term _ (Presyntax.Pattern _ (Presyntax.ConOrVar prename@(Name.Pre name) [])) type_) -> do
      maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) prename
      case maybeScopeEntry of
        Just (Scope.Constructors _) ->
          fail "No match instantitation"

        _ ->
          pure $ pure (Name name, Lazy $ pure term, Lazy $ pure type_)

    (Match _ _ (Presyntax.Pattern _ (Presyntax.Forced _)) _) ->
      pure mempty

    _ ->
      fail "No match instantitation"

solved :: Context v -> [Match] -> M (Maybe PatternInstantiation)
solved context =
  runMaybeT . fmap mconcat . traverse (matchInstantiation context)

-------------------------------------------------------------------------------

findConstructorMatch
  :: Context v
  -> [Match]
  -> M (Maybe (Var, Span.Relative, Name.QualifiedConstructor, Domain.Type))
findConstructorMatch context matches =
    case matches of
      [] ->
        pure Nothing

      Match (Domain.Neutral (Domain.Var x) Tsil.Empty) _ (Presyntax.Pattern span (Presyntax.ConOrVar name _)) type_:matches' -> do
        maybeScopeEntry <- fetch $ Query.ResolvedName (Context.scopeKey context) name
        case maybeScopeEntry of
          Just (Scope.Constructors constrs) -> do
            let
              expectedTypeName =
                Elaboration.getExpectedTypeName context type_
            maybeConstr <- Elaboration.resolveConstructor context name constrs expectedTypeName
            case maybeConstr of
              Nothing ->
                findConstructorMatch context matches'

              Just constr ->
                pure $ Just (x, span, constr, type_)

          _ ->
            findConstructorMatch context matches'

      _:matches' ->
        findConstructorMatch context matches'

splitConstructor
  :: Context v
  -> Config
  -> Var
  -> Span.Relative
  -> Name.QualifiedConstructor
  -> Domain.Type
  -> M (Syntax.Term v)
splitConstructor outerContext config scrutinee span (Name.QualifiedConstructor typeName _) outerType = do
  let
    goParams
      :: Context v
      -> [(Plicity, Lazy Domain.Value)]
      -> Domain.Spine
      -> Domain.Telescope Domain.Type [(Name.Constructor, Domain.Type)]
      -> M (Syntax.Type v)
    goParams context params conArgs dataTele =
      case (params, dataTele) of
        ([], Domain.Telescope.Empty constructors) -> do
          branches <- forM constructors $ \(constr, constrType) -> do
            let
              qualifiedConstr =
                Name.QualifiedConstructor typeName constr
            branchTele <- goConstrFields context qualifiedConstr conArgs constrType
            pure $ Syntax.Branch qualifiedConstr branchTele

          scrutinee' <- Elaboration.readback context (Domain.var scrutinee)
          pure $ Syntax.Case scrutinee' branches

        ((plicity1, param):params', Domain.Telescope.Extend _ _ plicity2 domainClosure)
          | plicity1 == plicity2 -> do
            domain <- domainClosure param
            goParams context params' (conArgs Tsil.:> (implicitise plicity1, param)) domain

        _ ->
          panic "goParams mismatch"

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
          result <- elaborate context' config
          pure $ Telescope.Empty result

  maybeDefinition <- fetch $ Query.ElaboratedDefinition typeName
  case maybeDefinition of
    Just (Syntax.DataDefinition tele, _) -> do
      tele' <- Evaluation.evaluateConstructorDefinitions (Domain.empty $ Context.scopeKey outerContext) tele
      outerType' <- Context.forceHead outerContext outerType
      case outerType' of
        Domain.Neutral (Domain.Global typeName') spine
          | typeName == typeName' ->
            goParams (Context.spanned span outerContext) (toList spine) mempty tele'

        _ ->
          panic "Matching outerType"

    _ ->
      panic "splitConstructor no data definition"

-------------------------------------------------------------------------------

findEqualityMatch
  :: Context v
  -> [Match]
  -> M (Maybe (Context v, Var, Lazy Domain.Type, Lazy Domain.Value, Lazy Domain.Value))
findEqualityMatch context matches =
  case matches of
    [] ->
      pure Nothing

    Match
      (Domain.Neutral (Domain.Var x) Tsil.Empty)
      _
      (Presyntax.Pattern _ Presyntax.WildcardPattern)
      (Builtin.Equals type_ value1 value2):matches' -> do
        value1' <- force value1
        value2' <- force value2
        result <- runExceptT $ Indices.unify context Flexibility.Rigid mempty value1' value2'
        case result of
          Left Indices.Nope ->
            pure Nothing

          Left Indices.Dunno ->
            findEqualityMatch context matches'

          Right context' ->
            pure $ Just (context', x, type_, value1, value2)

    _:matches' ->
      findEqualityMatch context matches'

splitEquality
  :: Context v
  -> Config
  -> Var
  -> Lazy Domain.Type
  -> Lazy Domain.Value
  -> Lazy Domain.Value
  -> M (Syntax.Term v)
splitEquality context config var type_ value1 value2 = do
  let
    context' =
      Context.define context var $ Lazy $ pure $ Builtin.Refl type_ value1 value2

  elaborate context' config

-------------------------------------------------------------------------------

uninhabitedScrutinee :: Context v -> Domain.Value -> M Bool
uninhabitedScrutinee context value = do
  value' <- Context.forceHead context value
  case value' of
    Domain.Neutral (Domain.Var var) spine -> do
      varType <- force $ Context.lookupVarType var context
      type_ <- applySpine varType spine
      uninhabitedType context 1 type_

    Domain.Neutral (Domain.Con constr) spine -> do
      constrType <- fetch $ Query.ConstructorType constr
      let
        args = snd <$> drop (Telescope.length constrType) (toList spine)
      args' <- mapM force args
      anyM (uninhabitedScrutinee context) args'

    _ ->
      pure False

  where
    applySpine :: Domain.Type -> Domain.Spine -> M Domain.Type
    applySpine type_ spine = do
      type' <- Context.forceHead context type_
      case (type', spine) of
        (_, Tsil.Empty) ->
          pure type'

        (Domain.Fun _ domain, spine' Tsil.:> (Explicit, _)) -> do
          domain' <- force domain
          applySpine domain' spine'

        (Domain.Pi _ _ plicity1 domainClosure, spine' Tsil.:> (plicity2, arg))
          | plicity1 == plicity2 -> do
            domain <- Evaluation.evaluateClosure domainClosure arg
            applySpine domain spine'

        _ ->
          panic "uninhabitedScrutinee.applySpine"

uninhabitedType :: Context v -> Int -> Domain.Type -> M Bool
uninhabitedType context fuel type_ = do
  type' <- Context.forceHead context type_
  case type' of
    Builtin.Equals _ value1 value2 -> do
      value1' <- force value1
      value2' <- force value2
      result <- runExceptT $ Indices.unify context Flexibility.Rigid mempty value1' value2'
      pure $ case result of
        Left Indices.Nope ->
          True

        Left Indices.Dunno ->
          False

        Right _ ->
          False

    Domain.Neutral (Domain.Global global) spine -> do
      maybeDefinitions <- fetch $ Query.ElaboratedDefinition global
      case maybeDefinitions of
        Just (Syntax.DataDefinition tele, _) -> do
          tele' <- Evaluation.evaluateConstructorDefinitions (Domain.empty $ Context.scopeKey context) tele
          tele'' <- Domain.Telescope.apply tele' $ toList spine
          case tele'' of
            Domain.Telescope.Empty constructors ->
              allM (uninhabitedConstrType context fuel . snd) constructors

            _ ->
              pure False

        _ ->
          pure False

    _ ->
      pure False

uninhabitedConstrType :: Context v -> Int -> Domain.Type -> M Bool
uninhabitedConstrType context fuel type_ =
  case fuel of
    0 ->
      pure False

    _ -> do
      type' <- Context.forceHead context type_
      case type' of
        Domain.Pi name source _ domainClosure -> do
          source' <- force source
          uninhabited <- uninhabitedType context (fuel - 1) source'
          if uninhabited then
            pure True

          else do
            (context', var) <- Context.extendUnnamed context name source
            domain <- Evaluation.evaluateClosure domainClosure $ Lazy $ pure $ Domain.var var
            uninhabitedConstrType context' fuel domain

        Domain.Fun source domain -> do
          source' <- force source
          uninhabited <- uninhabitedType context (fuel - 1) source'
          if uninhabited then
            pure True

          else do
            domain' <- force domain
            uninhabitedConstrType context fuel domain'

        _ ->
          pure False
