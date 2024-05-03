{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Elaboration.MetaInlining where

import Core.Binding (Binding)
import Core.Bindings (Bindings)
import qualified Core.Domain as Domain
import qualified Core.Syntax as Syntax
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import Data.EnumSet (EnumSet)
import qualified Data.EnumSet as EnumSet
import Data.Graph
import Data.OrderedHashMap (OrderedHashMap)
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Extra
import qualified Index.Map
import qualified Index.Map as Index (Map)
import Literal (Literal)
import qualified Meta
import Monad
import qualified Name
import Plicity
import qualified Postponement
import Protolude hiding (Type, evaluate)
import qualified Span
import Telescope (Telescope)
import qualified Telescope
import Var (Var)
import Prelude (Show (showsPrec))

inlineSolutions
  :: Syntax.MetaSolutions
  -> Syntax.Definition
  -> Syntax.Type Void
  -> M (Syntax.Definition, Syntax.Type Void)
inlineSolutions solutions def type_ = do
  solutionValues <- forM solutions \(metaTerm, metaType, metaOccurrences) -> do
    metaValue <- evaluate Environment.empty metaTerm
    metaType' <- evaluate Environment.empty metaType
    pure (metaValue, metaType', metaOccurrences)

  let sortedSolutions =
        acyclic
          <$> topoSortWith
            fst
            (\(_, (_, _, metaOccurrences)) -> EnumSet.toList metaOccurrences)
            (EnumMap.toList solutionValues)

      lookupMetaIndex metas index =
        EnumMap.findWithDefault
          (panic "Elaboration.MetaInlining.inlineSolutions: unknown index")
          index
          metas

      inlineTermSolutions :: Domain.Environment v -> Syntax.Term v -> M (Syntax.Term v)
      inlineTermSolutions env term = do
        let go :: (Meta.Index, (Value, Type, unused)) -> (Value, EnumMap Meta.Index (Var, [Maybe DuplicableValue])) -> M (Value, EnumMap Meta.Index (Var, [Maybe DuplicableValue]))
            go (index, (solutionValue, solutionType, _)) (value, metaVars) =
              case EnumMap.lookup index $ occurrencesMap value of
                Nothing ->
                  pure (value, metaVars)
                Just (occurrenceCount, duplicableArgs) -> do
                  solutionVar <- freshVar
                  let duplicableArgsList =
                        toList duplicableArgs

                      duplicableVars =
                        EnumSet.fromList
                          [ var
                          | Just (DuplicableVar var) <- duplicableArgsList
                          ]

                      (inlinedSolutionValue, inlinedSolutionType) =
                        unShared $ inlineArguments solutionValue solutionType duplicableArgsList mempty

                      value' =
                        unShared $
                          sharing value $
                            inlineIndex index duplicableVars (solutionVar, occurrenceCount, duplicableArgsList, inlinedSolutionValue, inlinedSolutionType) value

                      metaVars' =
                        EnumMap.insert index (solutionVar, duplicableArgsList) metaVars

                  pure (value', metaVars')
        value <- evaluate env term
        (inlinedValue, metaVars) <- foldrM go (value, mempty) sortedSolutions
        pure $
          readback env.indices (lookupMetaIndex metaVars) inlinedValue

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
        -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
        -> M (Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v)
      inlineTeleSolutions env tele =
        case tele of
          Telescope.Empty (Syntax.ConstructorDefinitions constrs) -> do
            constrs' <- OrderedHashMap.forMUnordered constrs $ inlineTermSolutions env
            pure $ Telescope.Empty (Syntax.ConstructorDefinitions constrs')
          Telescope.Extend name paramType plicity tele' -> do
            paramType' <- inlineTermSolutions env paramType
            (env', _) <- Environment.extend env
            tele'' <- inlineTeleSolutions env' tele'
            pure $ Telescope.Extend name paramType' plicity tele''

  inlinedType <- inlineTermSolutions Environment.empty type_
  inlinedDef <- inlineDefSolutions Environment.empty def

  pure
    ( inlinedDef
    , inlinedType
    )
  where
    acyclic (AcyclicSCC x) = x
    acyclic (CyclicSCC xs) = panic $ "Elaboration.MetaInlining.CyclicSCC " <> show (fst <$> xs)

data Value = Value !InnerValue Occurrences

instance Show Value where
  showsPrec d (Value v _) = showsPrec d v

data InnerValue
  = Var !Var
  | Global !Name.Qualified
  | Con !Name.QualifiedConstructor
  | Lit !Literal
  | Meta !Meta.Index (Tsil Value)
  | PostponedCheck !Postponement.Index !Value
  | LetsValue !InnerLets
  | Pi !Binding !Var !Type !Plicity !Type
  | Fun !Type !Plicity !Type
  | Lam !Bindings !Var !Type !Plicity !Value
  | App !Value !Plicity !Value
  | Case !Value !Type Branches !(Maybe Value)
  | Spanned !Span.Relative !InnerValue
  deriving (Show)

data Lets = Lets !InnerLets Occurrences

instance Show Lets where
  showsPrec d (Lets l _) = showsPrec d l

data InnerLets
  = LetType !Binding !Var !Type !Lets
  | Let !Bindings !Var !Value !Lets
  | In !InnerValue
  deriving (Show)

data DuplicableValue
  = DuplicableVar !Var
  | DuplicableGlobal !Name.Qualified
  | DuplicableCon !Name.QualifiedConstructor
  | DuplicableLit !Literal
  deriving (Eq, Show)

duplicableView :: Value -> Maybe DuplicableValue
duplicableView (Value value _) =
  case value of
    Var var ->
      Just $ DuplicableVar var
    Global global ->
      Just $ DuplicableGlobal global
    Con con ->
      Just $ DuplicableCon con
    Lit lit ->
      Just $ DuplicableLit lit
    _ ->
      Nothing

unduplicable :: DuplicableValue -> Value
unduplicable duplicableValue =
  case duplicableValue of
    DuplicableVar var ->
      makeVar var
    DuplicableGlobal global ->
      makeGlobal global
    DuplicableCon con ->
      makeCon con
    DuplicableLit lit ->
      makeLit lit

data Branches
  = ConstructorBranches !Name.Qualified (OrderedHashMap Name.Constructor ([Span.Relative], ([(Bindings, Var, Type, Plicity)], Value)))
  | LiteralBranches (OrderedHashMap Literal ([Span.Relative], Value))
  deriving (Show)

newtype Occurrences = Occurrences {unoccurrences :: EnumMap Meta.Index (Int, Tsil (Maybe DuplicableValue))}

instance Semigroup Occurrences where
  Occurrences occs1 <> Occurrences occs2 =
    Occurrences $
      EnumMap.unionWith
        (\(count1, args1) (count2, args2) -> (count1 + count2, Tsil.zipWith (\arg1 arg2 -> if arg1 == arg2 then arg1 else Nothing) args1 args2))
        occs1
        occs2

instance Monoid Occurrences where
  mempty = Occurrences mempty

occurrences :: Value -> Occurrences
occurrences (Value _ occs) = occs

letOccurrences :: Lets -> Occurrences
letOccurrences (Lets _ occs) = occs

occurrencesMap :: Value -> EnumMap Meta.Index (Int, Tsil (Maybe DuplicableValue))
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
    Occurrences (EnumMap.singleton index (1, duplicableView <$> arguments))
      <> foldMap occurrences arguments

makePostponedCheck :: Postponement.Index -> Value -> Value
makePostponedCheck index value =
  Value (PostponedCheck index value) $
    occurrences value

makeLets :: Lets -> Value
makeLets (Lets lets occs) =
  Value (LetsValue lets) occs

makeLetType :: Binding -> Var -> Type -> Lets -> Lets
makeLetType bindings var type_ lets =
  Lets (LetType bindings var type_ lets) $
    occurrences type_
      <> letOccurrences lets

makeLet :: Bindings -> Var -> Value -> Lets -> Lets
makeLet bindings var value lets =
  Lets (Let bindings var value lets) $
    occurrences value
      <> letOccurrences lets

makeIn :: Value -> Lets
makeIn (Value value occs) =
  Lets (In value) occs

makePi :: Binding -> Var -> Type -> Plicity -> Value -> Value
makePi binding var domain plicity target =
  Value (Pi binding var domain plicity target) $
    occurrences domain
      <> occurrences target

makeFun :: Type -> Plicity -> Type -> Value
makeFun domain plicity target =
  Value (Fun domain plicity target) $
    occurrences domain
      <> occurrences target

makeLam :: Bindings -> Var -> Type -> Plicity -> Value -> Value
makeLam bindings var type_ plicity body =
  Value (Lam bindings var type_ plicity body) $
    occurrences type_
      <> occurrences body

makeApp0 :: Value -> Plicity -> Value -> Value
makeApp0 fun@(Value fun' (Occurrences occs)) plicity arg =
  case (fun', plicity) of
    (Meta index args, Explicit) ->
      Value (Meta index (args Tsil.:> arg)) $
        Occurrences (EnumMap.adjust (second (Tsil.:> duplicableView arg)) index occs)
          <> occurrences arg
    _ ->
      makeApp fun plicity arg

makeApp :: Value -> Plicity -> Value -> Value
makeApp fun plicity arg =
  Value (App fun plicity arg) $
    occurrences fun
      <> occurrences arg

makeCase :: Value -> Type -> Branches -> Maybe Value -> Value
makeCase scrutinee type_ branches defaultBranch =
  Value (Case scrutinee type_ branches defaultBranch) $
    occurrences scrutinee
      <> branchOccurrences branches
      <> foldMap occurrences defaultBranch

branchOccurrences :: Branches -> Occurrences
branchOccurrences branches =
  case branches of
    ConstructorBranches _ constructorBranches ->
      foldMap
        ( \(_, (bindings, body)) ->
            foldMap (\(_, _, type_, _) -> occurrences type_) bindings
              <> occurrences body
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
    Syntax.PostponedCheck index term' ->
      makePostponedCheck index <$> evaluate env term'
    Syntax.Lets lets ->
      makeLets <$> evaluateLets env lets
    Syntax.Pi name domain plicity target -> do
      (env', var) <- Environment.extend env
      makePi name var
        <$> evaluate env domain
        <*> pure plicity
        <*> evaluate env' target
    Syntax.Fun domain plicity target ->
      makeFun
        <$> evaluate env domain
        <*> pure plicity
        <*> evaluate env target
    Syntax.Lam name type_ plicity body -> do
      (env', var) <- Environment.extend env
      makeLam name var
        <$> evaluate env type_
        <*> pure plicity
        <*> evaluate env' body
    Syntax.App function plicity argument ->
      makeApp0
        <$> evaluate env function
        <*> pure plicity
        <*> evaluate env argument
    Syntax.Case scrutinee type_ branches defaultBranch ->
      makeCase
        <$> evaluate env scrutinee
        <*> evaluate env type_
        <*> evaluateBranches env branches
        <*> mapM (evaluate env) defaultBranch
    Syntax.Spanned span term' ->
      makeSpanned span <$> evaluate env term'

evaluateLets :: Domain.Environment v -> Syntax.Lets v -> M Lets
evaluateLets env lets =
  case lets of
    Syntax.LetType name type_ lets' -> do
      (env', var) <- Environment.extend env
      makeLetType name var
        <$> evaluate env type_
        <*> evaluateLets env' lets'
    Syntax.Let name index value lets' ->
      makeLet name (Environment.lookupIndexVar index env)
        <$> evaluate env value
        <*> evaluateLets env lets'
    Syntax.In term ->
      makeIn <$> evaluate env term

evaluateBranches
  :: Domain.Environment v
  -> Syntax.Branches v
  -> M Branches
evaluateBranches env branches =
  case branches of
    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
      ConstructorBranches constructorTypeName <$> OrderedHashMap.mapMUnordered (mapM $ evaluateTelescope env) constructorBranches
    Syntax.LiteralBranches literalBranches ->
      LiteralBranches <$> OrderedHashMap.mapMUnordered (mapM $ evaluate env) literalBranches

evaluateTelescope
  :: Domain.Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M ([(Bindings, Var, Type, Plicity)], Value)
evaluateTelescope env tele =
  case tele of
    Telescope.Empty body -> do
      body' <- evaluate env body
      pure ([], body')
    Telescope.Extend name type_ plicity tele' -> do
      type' <- evaluate env type_
      (env', var) <- Environment.extend env
      (bindings, body) <- evaluateTelescope env' tele'
      pure ((name, var, type', plicity) : bindings, body)

readback :: Index.Map v Var -> (Meta.Index -> (Var, [Maybe x])) -> Value -> Syntax.Term v
readback env metas (Value value occs) =
  case value of
    Var var ->
      Syntax.Var $
        fromMaybe (panic "Elaboration.MetaInlining.readback Var") $
          Index.Map.elemIndex var env
    Global global ->
      Syntax.Global global
    Con con ->
      Syntax.Con con
    Lit lit ->
      Syntax.Lit lit
    Meta index arguments ->
      let (var, duplicableArgs) =
            metas index

          arguments' =
            snd <$> filter (isNothing . fst) (zip (duplicableArgs <> repeat Nothing) (toList arguments))
       in Syntax.apps
            ( Syntax.Var $
                fromMaybe (panic $ "Elaboration.MetaInlining.readback Meta " <> show index) $
                  Index.Map.elemIndex var env
            )
            ((,) Explicit . readback env metas <$> arguments')
    PostponedCheck index value' ->
      Syntax.PostponedCheck index $ readback env metas value'
    LetsValue lets ->
      Syntax.Lets $ readbackLets env metas $ Lets lets occs
    Pi name var domain plicity target ->
      Syntax.Pi
        name
        (readback env metas domain)
        plicity
        (readback (env Index.Map.:> var) metas target)
    Fun domain plicity target ->
      Syntax.Fun (readback env metas domain) plicity (readback env metas target)
    Lam name var type_ plicity body ->
      Syntax.Lam
        name
        (readback env metas type_)
        plicity
        (readback (env Index.Map.:> var) metas body)
    App function plicity argument ->
      Syntax.App (readback env metas function) plicity (readback env metas argument)
    Case scrutinee type_ branches defaultBranch ->
      Syntax.Case
        (readback env metas scrutinee)
        (readback env metas type_)
        (readbackBranches env metas branches)
        (readback env metas <$> defaultBranch)
    Spanned span value' ->
      Syntax.Spanned span (readback env metas (Value value' occs))

readbackLets
  :: Index.Map v Var
  -> (Meta.Index -> (Var, [Maybe var]))
  -> Lets
  -> Syntax.Lets v
readbackLets env metas (Lets lets occs) =
  case lets of
    LetType name var type_ lets' ->
      Syntax.LetType
        name
        (readback env metas type_)
        (readbackLets (env Index.Map.:> var) metas lets')
    Let name var value lets' ->
      Syntax.Let
        name
        (fromMaybe (panic "Elaboration.MetaInlining: indexless let") $ Index.Map.elemIndex var env)
        (readback env metas value)
        (readbackLets env metas lets')
    In term ->
      Syntax.In $ readback env metas $ Value term occs

readbackBranches
  :: Index.Map v Var
  -> (Meta.Index -> (Var, [Maybe var]))
  -> Branches
  -> Syntax.Branches v
readbackBranches env metas branches =
  case branches of
    ConstructorBranches constructorTypeName constructorBranches ->
      Syntax.ConstructorBranches constructorTypeName $
        fmap (uncurry $ readbackTelescope env metas) <$> constructorBranches
    LiteralBranches literalBranches ->
      Syntax.LiteralBranches $
        fmap (readback env metas) <$> literalBranches

readbackTelescope
  :: Index.Map v Var
  -> (Meta.Index -> (Var, [Maybe var]))
  -> [(Bindings, Var, Type, Plicity)]
  -> Value
  -> Telescope Bindings Syntax.Type Syntax.Term v
readbackTelescope env metas bindings body =
  case bindings of
    [] ->
      Telescope.Empty $ readback env metas body
    (name, var, type_, plicity) : bindings' -> do
      let env' = env Index.Map.:> var
      Telescope.Extend name (readback env metas type_) plicity (readbackTelescope env' metas bindings' body)

inlineArguments
  :: Value
  -> Value
  -> [Maybe DuplicableValue]
  -> EnumMap Var Value
  -> Shared (Value, Value)
inlineArguments value@(Value innerValue _) type_@(Value innerType _) args subst =
  case args of
    [] ->
      (,) <$> substitute subst value <*> substitute subst type_
    Just arg : args' ->
      case (innerValue, innerType) of
        (Lam _ var _ _ body, Pi _ var' _ _ target) ->
          let subst' =
                EnumMap.insert var (unduplicable arg) $
                  EnumMap.insert var' (unduplicable arg) subst
           in inlineArguments body target args' subst'
        _ ->
          (,) <$> substitute subst value <*> substitute subst type_
    Nothing : args' ->
      case (innerValue, innerType) of
        (Lam name var argType plicity1 body, Pi name' var' domain plicity2 target)
          | plicity1 == plicity2 ->
              sharing (value, type_) do
                argType' <- substitute subst argType
                domain' <- substitute subst domain
                (body', target') <- inlineArguments body target args' subst
                pure
                  ( makeLam name var argType' plicity1 body'
                  , makePi name' var' domain' plicity1 target'
                  )
        _ ->
          (,) <$> substitute subst value <*> substitute subst type_

substitute :: EnumMap Var Value -> Value -> Shared Value
substitute subst
  | EnumMap.null subst =
      pure
  | otherwise =
      go
  where
    go value@(Value innerValue occs) = sharing value case innerValue of
      Var var ->
        case EnumMap.lookup var subst of
          Nothing ->
            pure value
          Just value' -> do
            modified
            pure value'
      Global _ ->
        pure value
      Con _ ->
        pure value
      Lit _ ->
        pure value
      Meta index args ->
        makeMeta index <$> mapM go args
      PostponedCheck index value' ->
        makePostponedCheck index <$> go value'
      LetsValue lets ->
        makeLets <$> goLets (Lets lets occs)
      Pi name var domain plicity target ->
        makePi name var <$> go domain <*> pure plicity <*> go target
      Fun domain plicity target ->
        makeFun <$> go domain <*> pure plicity <*> go target
      Lam name var type_ plicity body ->
        makeLam name var <$> go type_ <*> pure plicity <*> go body
      App function plicity argument ->
        makeApp <$> go function <*> pure plicity <*> go argument
      Case scrutinee type_ branches defaultBranch ->
        makeCase
          <$> go scrutinee
          <*> go type_
          <*> ( case branches of
                  ConstructorBranches constructorTypeName constructorBranches ->
                    ConstructorBranches constructorTypeName
                      <$> OrderedHashMap.forMUnordered
                        constructorBranches
                        ( \(span, (bindings, body)) -> do
                            bindings' <- forM bindings \(name, var, bindingType, plicity) ->
                              (name,var,,plicity) <$> go bindingType

                            body' <- go body
                            pure (span, (bindings', body'))
                        )
                  LiteralBranches literalBranches ->
                    LiteralBranches
                      <$> OrderedHashMap.mapMUnordered (mapM go) literalBranches
              )
          <*> mapM go defaultBranch
      Spanned span value' ->
        makeSpanned span <$> go (Value value' occs)

    goLets :: Lets -> Shared Lets
    goLets lets@(Lets innerLets occs) =
      sharing lets case innerLets of
        LetType name var type_ lets' ->
          makeLetType name var <$> go type_ <*> goLets lets'
        Let name var value lets' ->
          makeLet name var <$> go value <*> goLets lets'
        In value ->
          makeIn <$> go (Value value occs)

data Shared a = Shared !Bool a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative Shared where
  pure =
    Shared False

  (<*>) =
    ap

instance Monad Shared where
  Shared p a >>= f = do
    let Shared q b =
          f a
    Shared (p || q) b

modified :: Shared ()
modified =
  Shared True ()

sharing :: a -> Shared a -> Shared a
sharing a (Shared modified_ a') =
  Shared modified_ if modified_ then a' else a

unShared :: Shared a -> a
unShared (Shared _ a) =
  a

inlineIndex
  :: Meta.Index
  -> EnumSet Var
  -> (Var, Int, [Maybe DuplicableValue], Value, Value)
  -> Value
  -> Shared Value
inlineIndex index targetScope solution@(solutionVar, occurrenceCount, duplicableArgs, solutionValue, solutionType) value@(Value innerValue occs) = do
  let recurse value' =
        sharing value' $
          inlineIndex index targetScope solution value'

      recurseScope var value' =
        sharing value' $
          inlineIndex index (EnumSet.delete var targetScope) solution value'
  case innerValue of
    Meta index' args
      | index == index' -> do
          modified
          let remainingArgs =
                snd
                  <$> filter
                    (isNothing . fst)
                    (zip (duplicableArgs <> repeat Nothing) (toList args))
          pure $ foldl' (`makeApp` Explicit) solutionValue remainingArgs
    _
      | EnumSet.null targetScope && occurrenceCount > 1 ->
          if index `EnumMap.member` occurrencesMap value
            then do
              modified
              pure $
                makeLets $
                  makeLetType "meta" solutionVar solutionType $
                    makeLet "meta" solutionVar solutionValue $
                      makeIn value
            else pure value
    Var _ ->
      pure value
    Global _ ->
      pure value
    Con _ ->
      pure value
    Lit _ ->
      pure value
    Meta index' args -> do
      args' <- forM args $ inlineIndex index targetScope solution
      pure $ makeMeta index' args'
    PostponedCheck index' value' ->
      makePostponedCheck index' <$> recurse value'
    LetsValue lets ->
      makeLets <$> inlineLetsIndex index targetScope solution (Lets lets occs)
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
    Case scrutinee type_ branches defaultBranch -> do
      scrutinee' <- recurse scrutinee
      type' <- recurse type_
      branches' <- case branches of
        ConstructorBranches constructorTypeName constructorBranches ->
          ConstructorBranches constructorTypeName
            <$> OrderedHashMap.forMUnordered constructorBranches \(span, (bindings, body)) -> do
              let go targetScope' bindings' =
                    case bindings' of
                      [] -> do
                        body' <- sharing body $ inlineIndex index targetScope' solution body
                        pure ([], body')
                      (name, var, bindingType, plicity) : bindings'' -> do
                        bindingType' <- sharing bindingType $ inlineIndex index targetScope' solution bindingType
                        (bindings''', body') <- go (EnumSet.delete var targetScope') bindings''
                        pure ((name, var, bindingType', plicity) : bindings''', body')

              (bindings', body') <- go targetScope bindings
              pure (span, (bindings', body'))
        LiteralBranches literalBranches ->
          LiteralBranches <$> OrderedHashMap.mapMUnordered (mapM recurse) literalBranches
      defaultBranch' <- forM defaultBranch recurse
      pure $ makeCase scrutinee' type' branches' defaultBranch'
    Spanned span value' ->
      makeSpanned span <$> recurse (Value value' occs)

inlineLetsIndex :: Meta.Index -> EnumSet Var -> (Var, Int, [Maybe DuplicableValue], Value, Value) -> Lets -> Shared Lets
inlineLetsIndex index targetScope solution lets@(Lets innerLets occs) =
  sharing lets case innerLets of
    LetType name var type_ lets' ->
      makeLetType name var <$> recurseValue type_ <*> recurseScope var lets'
    Let name var value lets' ->
      makeLet name var <$> recurseValue value <*> recurseLets lets'
    In value ->
      makeIn <$> recurseValue (Value value occs)
  where
    recurseLets =
      inlineLetsIndex index targetScope solution

    recurseScope var =
      inlineLetsIndex index (EnumSet.delete var targetScope) solution

    recurseValue =
      inlineIndex index targetScope solution
