{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Elaboration.Metas where

import Prelude (Show (showsPrec))
import Protolude hiding (Type, IntMap, evaluate)

import Data.Graph
import Data.IORef

import "this" Data.IntMap (IntMap)
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Extra
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import Plicity
import qualified "this" Data.IntMap as IntMap
import qualified Readback
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)
import qualified Var

inlineSolutions
  :: Syntax.MetaSolutions
  -> Syntax.Definition
  -> Syntax.Type Void
  -> M (Syntax.Definition, Syntax.Type Void)
inlineSolutions solutions def type_ = do
  solutionValues <- forM solutions $ \(metaTerm, metaType) -> do
    metaValue <- evaluate Readback.empty metaTerm
    metaType' <- evaluate Readback.empty metaType
    pure (metaValue, metaType')

  let
    sortedSolutions =
      acyclic <$>
      topoSortWith
        fst
        (\(_, (metaValue, metaType)) -> fst <$> IntMap.toList (void $ unoccurrences $ occurrences metaValue <> occurrences metaType))
        (IntMap.toList solutionValues)

    go (index, meta) (value', metaVars) = do
      (result, maybeSolution) <- inlineIndex index meta value'
      let
        metaVars' =
          case maybeSolution of
            Nothing ->
              metaVars

            Just solution ->
              IntMap.insert index solution metaVars

      pure (result, metaVars')

    lookupMetaIndex metas index =
      IntMap.lookupDefault
        (panic "Elaboration.Metas.inlineSolutions: unknown index")
        index
        metas

    inlineTermSolutions :: Readback.Environment v -> Syntax.Term v -> M (Syntax.Term v)
    inlineTermSolutions env term = do
      value <- evaluate env term
      (inlinedValue, metaVars) <- foldrM go (value, mempty) sortedSolutions
      pure $
        readback env (lookupMetaIndex metaVars) inlinedValue

    inlineDefSolutions :: Readback.Environment Void -> Syntax.Definition -> M Syntax.Definition
    inlineDefSolutions env def' =
      case def' of
        Syntax.TypeDeclaration declaredType -> do
          declaredType' <- inlineTermSolutions env declaredType
          pure $ Syntax.TypeDeclaration declaredType'

        Syntax.ConstantDefinition term -> do
          term' <- inlineTermSolutions env term
          pure $ Syntax.ConstantDefinition term'

        Syntax.DataDefinition tele -> do
          tele' <- inlineTeleSolutions env tele
          pure $ Syntax.DataDefinition tele'

    inlineTeleSolutions
      :: Readback.Environment v
      -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
      -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v)
    inlineTeleSolutions env tele =
      case tele of
        Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
          constrs' <- forM constrs $ \(constr, constrType) -> do
            constrType' <- inlineTermSolutions env constrType
            pure (constr, constrType')
          pure $ Telescope.Empty (Syntax.ConstructorDefinitions constrs')

        Telescope.Extend name paramType plicity tele' -> do
          paramType' <- inlineTermSolutions env paramType
          (env', _) <- Readback.extend env
          tele'' <- inlineTeleSolutions env' tele'
          pure $ Telescope.Extend name paramType' plicity tele''

  inlinedType <- inlineTermSolutions Readback.empty type_
  inlinedDef <- inlineDefSolutions Readback.empty def

  pure
    ( inlinedDef
    , inlinedType
    )

  where
    acyclic (AcyclicSCC x) = x
    acyclic (CyclicSCC _) = panic "Elaboration.Metas.CyclicSCC"

data InnerValue
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Meta !Meta.Index (Tsil Value)
  | Let !Name !Var !Value !Type !Value
  | Pi !Name !Var !Type !Plicity !Type
  | Fun !Type !Type
  | Lam !Name !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value [Branch]
  deriving Show

data Branch = Branch !Name.QualifiedConstructor [(Name, Var, Type, Plicity)] !Value
  deriving Show

newtype Occurrences = Occurrences { unoccurrences :: IntMap Meta.Index (Tsil (Maybe Var)) }

instance Semigroup Occurrences where
  Occurrences occs1 <> Occurrences occs2 =
    Occurrences $
      IntMap.unionWith
        (Tsil.zipWith (\arg1 arg2 -> if arg1 == arg2 then arg1 else Nothing))
        occs1
        occs2

instance Monoid Occurrences where
  mempty = Occurrences mempty

data Value = Value !InnerValue Occurrences

app :: Value -> Plicity -> Value -> InnerValue
app fun@(Value fun' _) plicity arg =
  case (fun', plicity) of
    (Meta index args, Explicit) ->
      Meta index $ args Tsil.:> arg

    _ ->
      App fun plicity arg

instance Show Value where
  showsPrec d (Value v _) = showsPrec d v

occurrences :: Value -> Occurrences
occurrences (Value _ occs) = occs

occurrencesMap :: Value -> IntMap Meta.Index (Tsil (Maybe Var))
occurrencesMap = unoccurrences . occurrences

type Type = Value

makeValue :: InnerValue -> Value
makeValue innerValue =
  Value innerValue $
    case innerValue of
      Var _ ->
        mempty

      Global _ ->
        mempty

      Con _ ->
        mempty

      Meta index arguments ->
        let
          varView (Value arg _) =
            case arg of
              Var v ->
                Just v

              _ ->
                Nothing
        in
        Occurrences (IntMap.singleton index (varView <$> arguments)) <>
        foldMap occurrences arguments

      Let _ _ term type_ body ->
        occurrences term <>
        occurrences type_ <>
        occurrences body

      Pi _ _ source _ domain ->
        occurrences source <>
        occurrences domain

      Fun source domain ->
        occurrences source <>
        occurrences domain

      Lam _ _ type_ _ body ->
        occurrences type_ <>
        occurrences body

      App function _ argument ->
        occurrences function <>
        occurrences argument

      Case scrutinee branches ->
        occurrences scrutinee <>
        mconcat
          [ foldMap (\(_, _, type_, _) -> occurrences type_) bindings <>
            occurrences body
          | Branch _ bindings body <- branches
          ]

evaluate :: Readback.Environment v -> Syntax.Term v -> M Value
evaluate env term =
  makeValue <$>
    case term of
      Syntax.Var index ->
        pure $ Var $ Readback.lookupIndexVar index env

      Syntax.Global global ->
        pure $ Global global

      Syntax.Con con ->
        pure $ Con con

      Syntax.Meta index ->
        pure $ Meta index mempty

      Syntax.Let name value type_ body -> do
        (env', var) <- Readback.extend env
        Let name var <$>
          evaluate env value <*>
          evaluate env type_ <*>
          evaluate env' body

      Syntax.Pi name source plicity domain -> do
        (env', var) <- Readback.extend env
        Pi name var <$>
          evaluate env source <*>
          pure plicity <*>
          evaluate env' domain

      Syntax.Fun source domain ->
        Fun <$>
          evaluate env source <*>
          evaluate env domain

      Syntax.Lam name type_ plicity body -> do
        (env', var) <- Readback.extend env
        Lam name var <$>
          evaluate env type_ <*>
          pure plicity <*>
          evaluate env' body

      Syntax.App function plicity argument ->
        app <$>
          evaluate env function <*>
          pure plicity <*>
          evaluate env argument

      Syntax.Case scrutinee branches ->
        Case <$>
          evaluate env scrutinee <*>
          mapM (evaluateBranch env) branches

evaluateBranch :: Readback.Environment v -> Syntax.Branch v -> M Branch
evaluateBranch outerEnv (Syntax.Branch constr outerTele) =
  uncurry (Branch constr) <$> go outerEnv outerTele
  where
    go
      :: Readback.Environment v
      -> Telescope Syntax.Type Syntax.Term v
      -> M ([(Name, Var, Type, Plicity)], Value)
    go env tele =
      case tele of
        Telescope.Empty body -> do
          body' <- evaluate env body
          pure ([], body')

        Telescope.Extend name type_ plicity tele' -> do
          type' <- evaluate env type_
          (env', var) <- Readback.extend env
          (bindings, body) <- go env' tele'
          pure ((name, var, type', plicity):bindings, body)

readback :: Readback.Environment v -> (Meta.Index -> (Var, [Maybe var])) -> Value -> Syntax.Term v
readback env metas (Value value _) =
  case value of
    Var var ->
      Syntax.Var $
        fromMaybe (panic "Elaboration.Metas.readback Var") $
          Readback.lookupVarIndex var env

    Global global ->
      Syntax.Global global

    Con global ->
      Syntax.Con global

    Meta index arguments ->
      let
        (var, varArgs) =
          metas index

        arguments' =
          snd <$> filter (isNothing . fst) (zip (varArgs <> repeat Nothing) (toList arguments))
      in
      Syntax.apps
        (Syntax.Var $
          fromMaybe (panic $ "Elaboration.Metas.readback Meta " <> show index) $
          Readback.lookupVarIndex var env)
        ((,) Explicit . readback env metas <$> arguments')

    Let name var value' type_ body ->
      Syntax.Let
        name
        (readback env metas value')
        (readback env metas type_)
        (readback (Readback.extendVar env var) metas body)

    Pi name var source plicity domain ->
      Syntax.Pi
        name
        (readback env metas source)
        plicity
        (readback (Readback.extendVar env var) metas domain)

    Fun source domain ->
      Syntax.Fun (readback env metas source) (readback env metas domain)

    Lam name var type_ plicity body ->
      Syntax.Lam
        name
        (readback env metas type_)
        plicity
        (readback (Readback.extendVar env var) metas body)

    App function plicity argument ->
      Syntax.App (readback env metas function) plicity (readback env metas argument)

    Case scrutinee branches ->
      Syntax.Case (readback env metas scrutinee) (map (readbackBranch env metas) branches)

readbackBranch
  :: Readback.Environment v
  -> (Meta.Index -> (Var, [Maybe var]))
  -> Branch
  -> Syntax.Branch v
readbackBranch outerEnv metas (Branch constr outerBindings body) =
  Syntax.Branch constr $
    go outerEnv outerBindings
  where
    go
      :: Readback.Environment v
      -> [(Name, Var, Type, Plicity)]
      -> Telescope Syntax.Type Syntax.Term v
    go env bindings =
      case bindings of
        [] ->
          Telescope.Empty $ readback env metas body

        (name, var, type_, plicity):bindings' -> do
          let
            env' =
              Readback.extendVar env var
          Telescope.Extend name (readback env metas type_) plicity (go env' bindings')

inlineArguments
  :: Value
  -> Value
  -> [Maybe Var]
  -> IntMap Var Value
  -> (Value, Value)
inlineArguments value@(Value innerValue _) type_@(Value innerType _) args subst =
  case args of
    [] ->
      (substitute subst value, substitute subst type_)

    Just argVar:args' ->
      case (innerValue, innerType) of
        (Lam _ var _ _ body, Pi _ var' _ _ domain) ->
          let
            subst' =
              IntMap.insert var (makeValue $ Var argVar) $
              IntMap.insert var' (makeValue $ Var argVar) subst
          in
          inlineArguments body domain args' subst'

        _ ->
          (substitute subst value, substitute subst type_)

    Nothing:args' ->
      case (innerValue, innerType) of
        (Lam name var argType plicity1 body, Pi name' var' source plicity2 domain)
          | plicity1 == plicity2 ->
            let
              argType' =
                substitute subst argType

              source' =
                substitute subst source

              (body', domain') =
                inlineArguments body domain args' subst
            in
            ( makeValue $ Lam name var argType' plicity1 body'
            , makeValue $ Pi name' var' source' plicity1 domain'
            )

        _ ->
          (substitute subst value, substitute subst type_)

substitute :: IntMap Var Value -> Value -> Value
substitute subst
  | IntMap.null subst =
    identity
  | otherwise =
    go
  where
    go value@(Value innerValue _) =
      case innerValue of
        Var var ->
          IntMap.lookupDefault value var subst

        Global _ ->
          value

        Con _ ->
          value

        Meta index args ->
          makeValue $ Meta index $ go <$> args

        Let name var value' type_ body ->
          makeValue $ Let name var (go value') (go type_) (go body)

        Pi name var source plicity domain ->
          makeValue $ Pi name var (go source) plicity (go domain)

        Fun source domain ->
          makeValue $ Fun (go source) (go domain)

        Lam name var type_ plicity body ->
          makeValue $ Lam name var (go type_) plicity (go body)

        App function plicity argument ->
          makeValue $ App (go function) plicity (go argument)

        Case scrutinee branches ->
          makeValue $
            Case
              (go scrutinee)
              [ Branch
                constr
                [ (name, var, go type_, plicity)
                | (name, var, type_, plicity) <- bindings
                ]
                (go body)
              | Branch constr bindings body <- branches
              ]

inlineIndex
  :: Meta.Index
  -> (Value, Value)
  -> Value
  -> M (Value, Maybe (Var, [Maybe Var]))
inlineIndex index solution@(solutionValue, solutionType) value@(Value innerValue _) =
  case innerValue of
    Var _ ->
      pure (value, Nothing)

    Global _ ->
      pure (value, Nothing)

    Con _ ->
      pure (value, Nothing)

    Meta index' args
      | index == index' ->
        case IntMap.lookup index $ occurrencesMap value of
          Just varArgs ->
            let
              varArgsList =
                toList varArgs

              remainingArgs =
                snd <$>
                  filter
                    (isNothing . fst)
                    (zip (varArgsList <> repeat Nothing) (toList args))

              (inlinedSolutionValue, _) =
                inlineArguments solutionValue solutionType varArgsList mempty
            in
            pure
              ( foldl' (\v1 v2 -> makeValue $ app v1 Explicit v2) inlinedSolutionValue remainingArgs
              , Nothing
              )

          Nothing ->
            panic "Elaboration.Metas.inlineIndex Nothing"

      | otherwise ->
        case Tsil.filter ((index `IntMap.member`) . occurrencesMap) args of
          Tsil.Empty ->
            pure
              ( foldl' (\v1 v2 -> makeValue $ app v1 Explicit v2) value args
              , Nothing
              )

          Tsil.Empty Tsil.:> _ -> do
            argResults <- mapM (inlineIndex index solution) args
            let
              (args', results) =
                Tsil.unzip argResults
            pure
              ( makeValue $ Meta index' args'
              , listToMaybe $ catMaybes $ toList results
              )

          _ ->
            letSolution

    Let name var value' type_ body ->
      inline3 (Let name var) value' type_ body

    Pi name var source plicity domain ->
      inline2 (flip (Pi name var) plicity) source domain

    Fun source domain ->
      inline2 Fun source domain

    Lam name var type_ plicity body ->
      inline2 (flip (Lam name var) plicity) type_ body

    App function plicity argument ->
      inline2 (flip app plicity) function argument

    Case scrutinee branches -> do
      let
        branchOccurrences =
          flip concatMap branches $ \(Branch _ bindings body) ->
            occurrencesMap body :
            [occurrencesMap type_ | (_, _, type_, _) <- bindings]
      case
        ( index `IntMap.member` occurrencesMap scrutinee
        , filter (index `IntMap.member`) branchOccurrences
        ) of
        (False, []) ->
          pure (value, Nothing)

        (True, []) -> do
          (scrutinee', result) <- inlineIndex index solution scrutinee
          pure
            ( makeValue $ Case scrutinee' branches
            , result
            )

        (False, [_]) -> do
          resultRef <- liftIO $ newIORef $ panic "Elaboration.Metas inlineIndex Case"
          branches' <- forM branches $ \(Branch constr bindings body) -> do
            bindings' <- forM bindings $ \(name, var, type_, plicity) ->
              if index `IntMap.member` occurrencesMap type_ then do
                (type', result) <- inlineIndex index solution type_
                liftIO $ writeIORef resultRef result
                pure (name, var, type', plicity)
              else
                pure (name, var, type_, plicity)
            if index `IntMap.member` occurrencesMap body then do
              (body', result) <- inlineIndex index solution body
              liftIO $ writeIORef resultRef result
              pure $ Branch constr bindings' body'
            else
              pure $ Branch constr bindings' body
          result <- liftIO $ readIORef resultRef
          pure
            ( makeValue $ Case scrutinee branches'
            , result
            )

        _ ->
          letSolution
  where
    letSolution =
      case IntMap.lookup index $ occurrencesMap value of
        Nothing ->
          pure (value, Nothing)

        Just varArgs -> do
          let
            varArgsList =
              toList varArgs

            (inlinedSolutionValue, inlinedSolutionType) =
              inlineArguments solutionValue solutionType varArgsList mempty
          solutionVar <- freshVar
          pure
            ( makeValue $ Let "meta" solutionVar inlinedSolutionValue inlinedSolutionType value
            , Just (solutionVar, varArgsList)
            )

    inline2 con value1 value2 =
      case
        ( index `IntMap.member` occurrencesMap value1
        , index `IntMap.member` occurrencesMap value2
        ) of
        (False, False) ->
          pure (value, Nothing)

        (True, False) -> do
          (value1', result) <- inlineIndex index solution value1
          pure
            ( makeValue $ con value1' value2
            , result
            )

        (False, True) -> do
          (value2', result) <- inlineIndex index solution value2
          pure
            ( makeValue $ con value1 value2'
            , result
            )

        _ ->
          letSolution

    inline3 con value1 value2 value3 =
      case
        ( index `IntMap.member` occurrencesMap value1
        , index `IntMap.member` occurrencesMap value2
        , index `IntMap.member` occurrencesMap value3
        ) of
        (False, False, False) ->
          pure (value, Nothing)

        (True, False, False) -> do
          (value1', result) <- inlineIndex index solution value1
          pure
            ( makeValue $ con value1' value2 value3
            , result
            )

        (False, True, False) -> do
          (value2', result) <- inlineIndex index solution value2
          pure
            ( makeValue $ con value1 value2' value3
            , result
            )

        (False, False, True) -> do
          (value3', result) <- inlineIndex index solution value3
          pure
            ( makeValue $ con value1 value2 value3'
            , result
            )

        _ ->
          letSolution
