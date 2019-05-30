{-# language OverloadedStrings #-}
module Elaboration.Metas where

import Prelude (Show (showsPrec))
import Protolude hiding (Type, IntMap, evaluate)

import Data.Graph

import Extra
import IntMap (IntMap)
import qualified IntMap
import qualified Meta
import Monad
import Name (Name)
import qualified Name
import qualified Readback
import qualified Syntax
import Tsil (Tsil)
import qualified Tsil
import Var (Var)
import qualified Var

inlineSolutions
  :: Syntax.MetaSolutions
  -> Syntax.Term Void
  -> Syntax.Type Void
  -> M (Syntax.Term Void, Syntax.Type Void)
inlineSolutions solutions term type_ = do
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

  value <- evaluate Readback.empty term
  typeValue <- evaluate Readback.empty type_

  let
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

  (inlinedValue, metaVars) <- foldrM go (value, mempty) sortedSolutions
  (inlinedType, typeMetaVars) <- foldrM go (typeValue, mempty) sortedSolutions

  let
    lookupMetaIndex metas index =
      IntMap.lookupDefault
        (panic "Elaboration.Metas.inlineSolutions: unknown index")
        index
        metas

  pure
    ( readback Readback.empty (lookupMetaIndex metaVars) inlinedValue
    , readback Readback.empty (lookupMetaIndex typeMetaVars) inlinedType
    )

  where
    acyclic (AcyclicSCC x) = x
    acyclic (CyclicSCC _) = panic "Elaboration.Metas.CyclicSCC"

data InnerValue
  = Var !Var
  | Meta !Meta.Index (Tsil Value)
  | Global !Name.Qualified
  | Let !Name !Var !Value !Type !Value
  | Pi !Name !Var !Type !Type
  | Fun !Type !Type
  | Lam !Name !Var !Type !Value
  | App !Value !Value
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

app :: Value -> Value -> InnerValue
app fun@(Value fun' _) arg =
  case fun' of
    Meta index args ->
      Meta index $ Tsil.Snoc args arg

    _ ->
      App fun arg

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

      Global _ ->
        mempty

      Let _ _ term type_ body ->
        occurrences term <>
        occurrences type_ <>
        occurrences body

      Pi _ _ source domain ->
        occurrences source <>
        occurrences domain

      Fun source domain ->
        occurrences source <>
        occurrences domain

      Lam _ _ type_ body ->
        occurrences type_ <>
        occurrences body

      App function argument ->
        occurrences function <>
        occurrences argument

evaluate :: Readback.Environment v -> Syntax.Term v -> M Value
evaluate env term =
  makeValue <$>
    case term of
      Syntax.Var index ->
        pure $ Var $ Readback.lookupIndexVar index env

      Syntax.Meta index ->
        pure $ Meta index mempty

      Syntax.Global global ->
        pure $ Global global

      Syntax.Let name value type_ body -> do
        (env', var) <- Readback.extend env
        Let name var <$>
          evaluate env value <*>
          evaluate env type_ <*>
          evaluate env' body

      Syntax.Pi name source domain -> do
        (env', var) <- Readback.extend env
        Pi name var <$>
          evaluate env source <*>
          evaluate env' domain

      Syntax.Fun source domain ->
        Fun <$>
          evaluate env source <*>
          evaluate env domain

      Syntax.Lam name type_ body -> do
        (env', var) <- Readback.extend env
        Lam name var <$>
          evaluate env type_ <*>
          evaluate env' body

      Syntax.App function argument ->
        app <$>
          evaluate env function <*>
          evaluate env argument

readback :: Readback.Environment v -> (Meta.Index -> (Var, [Maybe var])) -> Value -> Syntax.Term v
readback env metas (Value value _) =
  case value of
    Var var ->
      Syntax.Var $
        fromMaybe (panic "Elaboration.Metas.readback Var") $
          Readback.lookupVarIndex var env

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
        (readback env metas <$> arguments')

    Global global ->
      Syntax.Global global

    Let name var value' type_ body ->
      Syntax.Let
        name
        (readback env metas value')
        (readback env metas type_)
        (readback (Readback.extendVar env var) metas body)

    Pi name var source domain ->
      Syntax.Pi
        name
        (readback env metas source)
        (readback (Readback.extendVar env var) metas domain)

    Fun source domain ->
      Syntax.Fun (readback env metas source) (readback env metas domain)

    Lam name var type_ body ->
      Syntax.Lam
        name
        (readback env metas type_)
        (readback (Readback.extendVar env var) metas body)

    App function argument ->
      Syntax.App (readback env metas function) (readback env metas argument)

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
        (Lam _ var _ body, Pi _ var' _ domain) ->
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
        (Lam name var argType body, Pi name' var' source domain) ->
          let
            argType' =
              substitute subst argType

            source' =
              substitute subst source

            (body', domain') =
              inlineArguments body domain args' subst
          in
          ( makeValue $ Lam name var argType' body'
          , makeValue $ Pi name' var' source' domain'
          )

        _ ->
          (substitute subst value, substitute subst type_)

substitute :: IntMap Var Value -> Value -> Value
substitute subst
  | IntMap.null subst =
    identity
  | otherwise = go
  where
    go value@(Value innerValue _) =
      case innerValue of
        Var var ->
          IntMap.lookupDefault value var subst

        Meta index args ->
          makeValue $ Meta index $ go <$> args

        Global _ ->
          value

        Let name var value' type_ body ->
          makeValue $ Let name var (go value') (go type_) (go body)

        Pi name var source domain ->
          makeValue $ Pi name var (go source) (go domain)

        Fun source domain ->
          makeValue $ Fun (go source) (go domain)

        Lam name var type_ body ->
          makeValue $ Lam name var (go type_) (go body)

        App function argument ->
          makeValue $ App (go function) (go argument)

inlineIndex
  :: Meta.Index
  -> (Value, Value)
  -> Value
  -> M (Value, Maybe (Var, [Maybe Var]))
inlineIndex index solution@(solutionValue, solutionType) value@(Value innerValue _) =
  case innerValue of
    Var _ ->
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
              ( foldl' (\v1 v2 -> makeValue $ app v1 v2) inlinedSolutionValue remainingArgs
              , Nothing
              )

          Nothing ->
            panic "Elaboration.Metas.inlineIndex Nothing"

      | otherwise ->
        case Tsil.filter ((index `IntMap.member`) . occurrencesMap) args of
          Tsil.Nil ->
            pure
              ( foldl' (\v1 v2 -> makeValue $ app v1 v2) value args
              , Nothing
              )

          Tsil.Snoc Tsil.Nil _ -> do
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

    Global _ ->
      pure (value, Nothing)

    Let name var value' type_ body ->
      inline3 (Let name var) value' type_ body

    Pi name var source domain ->
      inline2 (Pi name var) source domain

    Fun source domain ->
      inline2 Fun source domain

    Lam name var type_ body ->
      inline2 (Lam name var) type_ body

    App function argument ->
      inline2 app function argument
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
