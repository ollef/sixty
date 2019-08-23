{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
module Elaboration.Metas where

import Prelude (Show (showsPrec))
import Protolude hiding (Type, IntMap, IntSet, evaluate)

import Data.HashMap.Lazy (HashMap)
import Data.Graph

import "this" Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
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

    lookupMetaIndex metas index =
      IntMap.lookupDefault
        (panic "Elaboration.Metas.inlineSolutions: unknown index")
        index
        metas

    inlineTermSolutions :: Readback.Environment v -> Syntax.Term v -> M (Syntax.Term v)
    inlineTermSolutions env term = do
      let
        go :: (Meta.Index, (Value, Type)) -> (Value, IntMap Meta.Index (Var, [Maybe Var])) -> M (Value, IntMap Meta.Index (Var, [Maybe Var]))
        go (index, (solutionValue, solutionType)) (value, metaVars) =
          case IntMap.lookup index $ occurrencesMap value of
            Nothing ->
              pure (value, metaVars)

            Just varArgs -> do
              solutionVar <- freshVar
              let
                varArgsList =
                  toList varArgs

                (inlinedSolutionValue, inlinedSolutionType) =
                  inlineArguments solutionValue solutionType varArgsList mempty

                Shared _ value' =
                  sharing value' $
                    inlineIndex index (IntSet.fromList $ catMaybes varArgsList) (solutionVar, varArgsList, inlinedSolutionValue, inlinedSolutionType) value

                metaVars' =
                  IntMap.insert index (solutionVar, varArgsList) metaVars

              pure (value', metaVars')
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
  | Case !Value Branches !(Maybe Value)
  deriving Show

type Branches = HashMap Name.QualifiedConstructor ([(Name, Var, Type, Plicity)], Value)

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

instance Show Value where
  showsPrec d (Value v _) = showsPrec d v

occurrences :: Value -> Occurrences
occurrences (Value _ occs) = occs

occurrencesMap :: Value -> IntMap Meta.Index (Tsil (Maybe Var))
occurrencesMap = unoccurrences . occurrences

type Type = Value

makeVar :: Var -> Value
makeVar v =
  Value (Var v) mempty

makeGlobal :: Name.Qualified -> Value
makeGlobal n =
  Value (Global n) mempty

makeCon :: Name.QualifiedConstructor -> Value
makeCon c =
  Value (Con c) mempty

makeMeta :: Meta.Index -> Tsil Value -> Value
makeMeta index arguments =
  Value (Meta index arguments) $
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

makeLet :: Name -> Var -> Value -> Type -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value <>
    occurrences type_ <>
    occurrences body

makePi :: Name -> Var -> Type -> Plicity -> Value -> Value
makePi name var source plicity domain =
  Value (Pi name var source plicity domain) $
    occurrences source <>
    occurrences domain

makeFun :: Type -> Type -> Value
makeFun source domain =
  Value (Fun source domain) $
    occurrences source <>
    occurrences domain

makeLam :: Name -> Var -> Type -> Plicity -> Value -> Value
makeLam name var type_ plicity body =
  Value (Lam name var type_ plicity body) $
    occurrences type_ <>
    occurrences body

makeApp0 :: Value -> Plicity -> Value -> Value
makeApp0 fun@(Value fun' _) plicity arg =
  case (fun', plicity) of
    (Meta index args, Explicit) ->
      makeMeta index $ args Tsil.:> arg

    _ ->
      makeApp fun plicity arg

makeApp :: Value -> Plicity -> Value -> Value
makeApp fun plicity arg =
  Value (App fun plicity arg) $
    occurrences fun <>
    occurrences arg

makeCase :: Value -> Branches -> Maybe Value -> Value
makeCase scrutinee branches defaultBranch =
  Value (Case scrutinee branches defaultBranch) $
    occurrences scrutinee <>
    foldMap
      (\(bindings, body) ->
        foldMap (\(_, _, type_, _) -> occurrences type_) bindings <>
          occurrences body
      )
      branches <>
    foldMap occurrences defaultBranch

evaluate :: Readback.Environment v -> Syntax.Term v -> M Value
evaluate env term =
  case term of
    Syntax.Var index ->
      pure $ makeVar $ Readback.lookupIndexVar index env

    Syntax.Global global ->
      pure $ makeGlobal global

    Syntax.Con con ->
      pure $ makeCon con

    Syntax.Meta index ->
      pure $ makeMeta index mempty

    Syntax.Let name value type_ body -> do
      (env', var) <- Readback.extend env
      makeLet name var <$>
        evaluate env value <*>
        evaluate env type_ <*>
        evaluate env' body

    Syntax.Pi name source plicity domain -> do
      (env', var) <- Readback.extend env
      makePi name var <$>
        evaluate env source <*>
        pure plicity <*>
        evaluate env' domain

    Syntax.Fun source domain ->
      makeFun <$>
        evaluate env source <*>
        evaluate env domain

    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Readback.extend env
      makeLam name var <$>
        evaluate env type_ <*>
        pure plicity <*>
        evaluate env' body

    Syntax.App function plicity argument ->
      makeApp0 <$>
        evaluate env function <*>
        pure plicity <*>
        evaluate env argument

    Syntax.Case scrutinee branches defaultBranch ->
      makeCase <$>
        evaluate env scrutinee <*>
        mapM (evaluateBranch env) branches <*>
        mapM (evaluate env) defaultBranch

evaluateBranch
  :: Readback.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M ([(Name, Var, Type, Plicity)], Value)
evaluateBranch env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body
      pure ([], body')

    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate env type_
      (env', var) <- Readback.extend env
      (bindings, body) <- evaluateBranch env' tele'
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

    Case scrutinee branches defaultBranch ->
      Syntax.Case
        (readback env metas scrutinee)
        (map (uncurry $ readbackBranch env metas) branches)
        (readback env metas <$> defaultBranch)

readbackBranch
  :: Readback.Environment v
  -> (Meta.Index -> (Var, [Maybe var]))
  -> [(Name, Var, Type, Plicity)]
  -> Value
  -> Telescope Syntax.Type Syntax.Term v
readbackBranch env metas bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env metas body

    (name, var, type_, plicity):bindings' -> do
      let
        env' =
          Readback.extendVar env var
      Telescope.Extend name (readback env metas type_) plicity (readbackBranch env' metas bindings' body)

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
              IntMap.insert var (makeVar argVar) $
              IntMap.insert var' (makeVar argVar) subst
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
            ( makeLam name var argType' plicity1 body'
            , makePi name' var' source' plicity1 domain'
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
          makeMeta index $ go <$> args

        Let name var value' type_ body ->
          makeLet name var (go value') (go type_) (go body)

        Pi name var source plicity domain ->
          makePi name var (go source) plicity (go domain)

        Fun source domain ->
          makeFun (go source) (go domain)

        Lam name var type_ plicity body ->
          makeLam name var (go type_) plicity (go body)

        App function plicity argument ->
          makeApp (go function) plicity (go argument)

        Case scrutinee branches defaultBranch ->
          makeCase
            (go scrutinee)
            (foreach branches $ \(bindings, body) ->
              ( [ (name, var, go type_, plicity)
                | (name, var, type_, plicity) <- bindings
                ]
              , go body
              )
            )
            (go <$> defaultBranch)

data Shared a = Shared !Bool a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative Shared where
  pure =
    Shared False

  (<*>) =
    ap

instance Monad Shared where
  Shared p a >>= f = do
    let
      Shared q b =
        f a
    Shared (p || q) b

modified :: Shared ()
modified =
  Shared True ()

sharing :: a -> Shared a -> Shared a
sharing a (Shared modified_ a') =
  Shared modified_ $
    if modified_ then
      a'

    else
      a

inlineIndex
  :: Meta.Index
  -> IntSet Var
  -> (Var, [Maybe Var], Value, Value)
  -> Value
  -> Shared Value
inlineIndex index targetScope solution@ ~(solutionVar, varArgs, solutionValue, solutionType) value@(Value innerValue _)
  | IntSet.null targetScope = do
    modified
    pure $ makeLet "meta" solutionVar solutionValue solutionType value
  | otherwise = do
    let
      recurse value' =
        sharing value' $
          inlineIndex index targetScope solution value'

      recurseScope var value' =
        sharing value' $
          inlineIndex index (IntSet.delete var targetScope) solution value'

    case innerValue of
      Var _ ->
        pure value

      Global _ ->
        pure value

      Con _ ->
        pure value

      Meta index' args
        | index == index' -> do
          modified
          let
            remainingArgs =
              snd <$>
                filter
                  (isNothing . fst)
                  (zip (varArgs <> repeat Nothing) (toList args))
          pure $ foldl' (\v1 v2 -> makeApp v1 Explicit v2) solutionValue remainingArgs

        | otherwise -> do
          args' <- forM args $ inlineIndex index targetScope solution
          pure $ makeMeta index' args'

      Let name var value' type_ body -> do
        value'' <- recurse value'
        type' <- recurse type_
        body' <- recurseScope var body
        pure $ makeLet name var value'' type' body'

      Pi name var source plicity domain -> do
        source' <- recurse source
        domain' <- recurseScope var domain
        pure $ makePi name var source' plicity domain'

      Fun source domain -> do
        source' <- recurse source
        domain' <- recurse domain
        pure $ makeFun source' domain'

      Lam name var type_ plicity body -> do
        type' <- recurse type_
        body' <- recurseScope var body
        pure $ makeLam name var type' plicity body'

      App function plicity argument -> do
        function' <- recurse function
        argument' <- recurse argument
        pure $ makeApp function' plicity argument'

      Case scrutinee branches defaultBranch -> do
        scrutinee' <- recurse scrutinee
        branches' <- forM branches $ \(bindings, body) -> do
          let
            go targetScope' bindings' =
              case bindings' of
                [] -> do
                  body' <- sharing body $ inlineIndex index targetScope' solution body
                  pure ([], body')

                (name, var, type_, plicity):bindings'' -> do
                  type' <- sharing type_ $ inlineIndex index targetScope' solution type_
                  (bindings''', body') <- go (IntSet.delete var targetScope') bindings''
                  pure ((name, var, type', plicity):bindings''', body')

          (bindings', body') <- go targetScope bindings
          pure (bindings', body')
        defaultBranch' <- forM defaultBranch recurse
        pure $ makeCase scrutinee' branches' defaultBranch'
