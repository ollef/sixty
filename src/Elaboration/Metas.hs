{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveTraversable #-}
{-# language OverloadedStrings #-}
module Elaboration.Metas where

import Prelude (Show (showsPrec))
import Protolude hiding (Type, IntMap, IntSet, evaluate)

import Data.Graph
import Data.HashMap.Lazy (HashMap)

import Binding (Binding)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Domain
import qualified Environment
import Extra
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import qualified Scope
import qualified Span
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope
import Var (Var)
import qualified Var

inlineSolutions
  :: Scope.KeyedName
  -> Syntax.MetaSolutions
  -> Syntax.Definition
  -> Syntax.Type Void
  -> M (Syntax.Definition, Syntax.Type Void)
inlineSolutions scopeKey solutions def type_ = do
  solutionValues <- forM solutions $ \(metaTerm, metaType) -> do
    metaValue <- evaluate (Environment.empty scopeKey) metaTerm
    metaType' <- evaluate (Environment.empty scopeKey) metaType
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

    inlineTermSolutions :: Domain.Environment v -> Syntax.Term v -> M (Syntax.Term v)
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
                  sharing value $
                    inlineIndex index (IntSet.fromList $ catMaybes varArgsList) (solutionVar, varArgsList, inlinedSolutionValue, inlinedSolutionType) value

                metaVars' =
                  IntMap.insert index (solutionVar, varArgsList) metaVars

              pure (value', metaVars')
      value <- evaluate env term
      (inlinedValue, metaVars) <- foldrM go (value, mempty) sortedSolutions
      pure $
        readback env (lookupMetaIndex metaVars) inlinedValue

    inlineDefSolutions :: Domain.Environment Void -> Syntax.Definition -> M Syntax.Definition
    inlineDefSolutions env def' =
      case def' of
        Syntax.TypeDeclaration declaredType -> do
          declaredType' <- inlineTermSolutions env declaredType
          pure $ Syntax.TypeDeclaration declaredType'

        Syntax.ConstantDefinition term -> do
          term' <- inlineTermSolutions env term
          pure $ Syntax.ConstantDefinition term'

        Syntax.DataDefinition boxity tele -> do
          tele' <- inlineTeleSolutions env tele
          pure $ Syntax.DataDefinition boxity tele'

    inlineTeleSolutions
      :: Domain.Environment v
      -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
      -> M (Telescope Syntax.Type Syntax.ConstructorDefinitions v)
    inlineTeleSolutions env tele =
      case tele of
        Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
          constrs' <- forM constrs $ inlineTermSolutions env
          pure $ Telescope.Empty (Syntax.ConstructorDefinitions constrs')

        Telescope.Extend name paramType plicity tele' -> do
          paramType' <- inlineTermSolutions env paramType
          (env', _) <- Environment.extend env
          tele'' <- inlineTeleSolutions env' tele'
          pure $ Telescope.Extend name paramType' plicity tele''

  inlinedType <- inlineTermSolutions (Environment.empty scopeKey) type_
  inlinedDef <- inlineDefSolutions (Environment.empty scopeKey) def

  pure
    ( inlinedDef
    , inlinedType
    )

  where
    acyclic (AcyclicSCC x) = x
    acyclic (CyclicSCC _) = panic "Elaboration.Metas.CyclicSCC"

data Value = Value !InnerValue Occurrences

instance Show Value where
  showsPrec d (Value v _) = showsPrec d v

data InnerValue
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index (Tsil Value)
  | Let !Binding !Var !Value !Type !Value
  | Pi !Binding !Var !Type !Plicity !Type
  | Fun !Type !Plicity !Type
  | Lam !Binding !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value Branches !(Maybe Value)
  | Spanned !Span.Relative !InnerValue
  deriving Show

data Branches
  = ConstructorBranches (HashMap Name.QualifiedConstructor ([Span.Relative], ([(Binding, Var, Type, Plicity)], Value)))
  | LiteralBranches (HashMap Literal ([Span.Relative], Value))
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

makeLit :: Literal -> Value
makeLit lit =
  Value (Lit lit) mempty

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

makeLet :: Binding -> Var -> Value -> Type -> Value -> Value
makeLet name var value type_ body =
  Value (Let name var value type_ body) $
    occurrences value <>
    occurrences type_ <>
    occurrences body

makePi :: Binding -> Var -> Type -> Plicity -> Value -> Value
makePi name var domain plicity target =
  Value (Pi name var domain plicity target) $
    occurrences domain <>
    occurrences target

makeFun :: Type -> Plicity -> Type -> Value
makeFun domain plicity target =
  Value (Fun domain plicity target) $
    occurrences domain <>
    occurrences target

makeLam :: Binding -> Var -> Type -> Plicity -> Value -> Value
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
    branchOccurrences branches <>
    foldMap occurrences defaultBranch

branchOccurrences :: Branches -> Occurrences
branchOccurrences branches =
  case branches of
    ConstructorBranches constructorBranches ->
      foldMap
        (\(_, (bindings, body)) ->
          foldMap (\(_, _, type_, _) -> occurrences type_) bindings <>
            occurrences body
        )
        constructorBranches

    LiteralBranches literalBranches ->
      foldMap (occurrences . snd) literalBranches

makeSpanned :: Span.Relative -> Value -> Value
makeSpanned span (Value innerValue occs) =
  Value (Spanned span innerValue) occs

evaluate :: Domain.Environment v -> Syntax.Term v -> M Value
evaluate env term =
  case term of
    Syntax.Var index ->
      pure $ makeVar $ Environment.lookupIndexVar index env

    Syntax.Global global ->
      pure $ makeGlobal global

    Syntax.Con con ->
      pure $ makeCon con

    Syntax.Lit lit ->
      pure $ makeLit lit

    Syntax.Meta index ->
      pure $ makeMeta index mempty

    Syntax.Let name value type_ body -> do
      (env', var) <- Environment.extend env
      makeLet name var <$>
        evaluate env value <*>
        evaluate env type_ <*>
        evaluate env' body

    Syntax.Pi name domain plicity target -> do
      (env', var) <- Environment.extend env
      makePi name var <$>
        evaluate env domain <*>
        pure plicity <*>
        evaluate env' target

    Syntax.Fun domain plicity target ->
      makeFun <$>
        evaluate env domain <*>
        pure plicity <*>
        evaluate env target

    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Environment.extend env
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
        evaluateBranches env branches <*>
        mapM (evaluate env) defaultBranch

    Syntax.Spanned span term' ->
      makeSpanned span <$> evaluate env term'

evaluateBranches
  :: Domain.Environment v
  -> Syntax.Branches v
  -> M Branches
evaluateBranches env branches =
  case branches of
    Syntax.ConstructorBranches constructorBranches ->
      ConstructorBranches <$> mapM (mapM $ evaluateTelescope env) constructorBranches

    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> mapM (mapM $ evaluate env) literalBranches

evaluateTelescope
  :: Domain.Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> M ([(Binding, Var, Type, Plicity)], Value)
evaluateTelescope env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body
      pure ([], body')

    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate env type_
      (env', var) <- Environment.extend env
      (bindings, body) <- evaluateTelescope env' tele'
      pure ((name, var, type', plicity):bindings, body)

readback :: Domain.Environment v -> (Meta.Index -> (Var, [Maybe var])) -> Value -> Syntax.Term v
readback env metas (Value value occs) =
  case value of
    Var var ->
      Syntax.Var $
        fromMaybe (panic "Elaboration.Metas.readback Var") $
          Environment.lookupVarIndex var env

    Global global ->
      Syntax.Global global

    Con con ->
      Syntax.Con con

    Lit lit ->
      Syntax.Lit lit

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
          Environment.lookupVarIndex var env)
        ((,) Explicit . readback env metas <$> arguments')

    Let name var value' type_ body ->
      Syntax.Let
        name
        (readback env metas value')
        (readback env metas type_)
        (readback (Environment.extendVar env var) metas body)

    Pi name var domain plicity target ->
      Syntax.Pi
        name
        (readback env metas domain)
        plicity
        (readback (Environment.extendVar env var) metas target)

    Fun domain plicity target ->
      Syntax.Fun (readback env metas domain) plicity (readback env metas target)

    Lam name var type_ plicity body ->
      Syntax.Lam
        name
        (readback env metas type_)
        plicity
        (readback (Environment.extendVar env var) metas body)

    App function plicity argument ->
      Syntax.App (readback env metas function) plicity (readback env metas argument)

    Case scrutinee branches defaultBranch ->
      Syntax.Case
        (readback env metas scrutinee)
        (readbackBranches env metas branches)
        (readback env metas <$> defaultBranch)

    Spanned span value' ->
      Syntax.Spanned span (readback env metas (Value value' occs))

readbackBranches
  :: Domain.Environment v
  -> (Meta.Index -> (Var, [Maybe var]))
  -> Branches
  -> Syntax.Branches v
readbackBranches env metas branches =
  case branches of
    ConstructorBranches constructorBranches ->
      Syntax.ConstructorBranches $
        fmap (uncurry $ readbackTelescope env metas) <$> constructorBranches

    LiteralBranches literalBranches ->
      Syntax.LiteralBranches $
        fmap (readback env metas) <$> literalBranches

readbackTelescope
  :: Domain.Environment v
  -> (Meta.Index -> (Var, [Maybe var]))
  -> [(Binding, Var, Type, Plicity)]
  -> Value
  -> Telescope Syntax.Type Syntax.Term v
readbackTelescope env metas bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env metas body

    (name, var, type_, plicity):bindings' -> do
      let
        env' =
          Environment.extendVar env var
      Telescope.Extend name (readback env metas type_) plicity (readbackTelescope env' metas bindings' body)

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
        (Lam _ var _ _ body, Pi _ var' _ _ target) ->
          let
            subst' =
              IntMap.insert var (makeVar argVar) $
              IntMap.insert var' (makeVar argVar) subst
          in
          inlineArguments body target args' subst'

        _ ->
          (substitute subst value, substitute subst type_)

    Nothing:args' ->
      case (innerValue, innerType) of
        (Lam name var argType plicity1 body, Pi name' var' domain plicity2 target)
          | plicity1 == plicity2 ->
            let
              argType' =
                substitute subst argType

              domain' =
                substitute subst domain

              (body', target') =
                inlineArguments body target args' subst
            in
            ( makeLam name var argType' plicity1 body'
            , makePi name' var' domain' plicity1 target'
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
    go value@(Value innerValue occs) =
      case innerValue of
        Var var ->
          IntMap.lookupDefault value var subst

        Global _ ->
          value

        Con _ ->
          value

        Lit _ ->
          value

        Meta index args ->
          makeMeta index $ go <$> args

        Let name var value' type_ body ->
          makeLet name var (go value') (go type_) (go body)

        Pi name var domain plicity target ->
          makePi name var (go domain) plicity (go target)

        Fun domain plicity target ->
          makeFun (go domain) plicity (go target)

        Lam name var type_ plicity body ->
          makeLam name var (go type_) plicity (go body)

        App function plicity argument ->
          makeApp (go function) plicity (go argument)

        Case scrutinee branches defaultBranch ->
          makeCase
            (go scrutinee)
            (case branches of
              ConstructorBranches constructorBranches ->
                ConstructorBranches $
                  foreach constructorBranches $ \(span, (bindings, body)) ->
                    ( span
                    , ( [ (name, var, go type_, plicity)
                        | (name, var, type_, plicity) <- bindings
                        ]
                      , go body
                      )
                    )
              LiteralBranches literalBranches ->
                LiteralBranches $
                  foreach literalBranches $ second go
            )
            (go <$> defaultBranch)

        Spanned span value' ->
          makeSpanned span $ go (Value value' occs)

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
inlineIndex index targetScope solution@ ~(solutionVar, varArgs, solutionValue, solutionType) value@(Value innerValue occs)
  | IntSet.null targetScope =
    if index `IntMap.member` occurrencesMap value then do
      modified
      pure $ makeLet "meta" solutionVar solutionValue solutionType value

    else
      pure value

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

      Lit _ ->
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

      Pi name var domain plicity target -> do
        domain' <- recurse domain
        target' <- recurseScope var target
        pure $ makePi name var domain' plicity target'

      Fun domain plicity target -> do
        domain' <- recurse domain
        target' <- recurse target
        pure $ makeFun domain' plicity target'

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
        branches' <- case branches of
          ConstructorBranches constructorBranches ->
            fmap ConstructorBranches $ forM constructorBranches $ \(span, (bindings, body)) -> do
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
              pure (span, (bindings', body'))

          LiteralBranches literalBranches ->
            LiteralBranches <$> mapM (mapM recurse) literalBranches
        defaultBranch' <- forM defaultBranch recurse
        pure $ makeCase scrutinee' branches' defaultBranch'

      Spanned span value' ->
        makeSpanned span <$> recurse (Value value' occs)
