{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module ClosureConvertedToAssembly where

import qualified Assembly
import Boxity
import qualified Builtin
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Representation
import qualified ClosureConverted.Syntax as Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Core.Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index
import Literal (Literal)
import qualified Literal
import qualified Module
import Monad
import Name (Name (Name))
import qualified Name
import Protolude hiding (IntMap, local, moduleName, state, typeOf)
import Query (Query)
import qualified Query
import Representation (Representation)
import qualified Representation
import Rock
import qualified Scope
import Telescope (Telescope)
import qualified Telescope
import Var (Var (Var))

newtype Builder a = Builder (StateT BuilderState M a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFetch Query, MonadState BuilderState)

data BuilderState = BuilderState
  { _fresh :: !Int
  , _instructions :: Tsil (Assembly.Instruction Assembly.BasicBlock)
  }

runBuilder :: Builder a -> M a
runBuilder (Builder s) =
  evalStateT
    s
    BuilderState
      { _fresh = 0
      , _instructions = mempty
      }

subBuilder :: Builder a -> Builder (a, [Assembly.Instruction Assembly.BasicBlock])
subBuilder (Builder s) = do
  state <- get
  (a, state') <- Builder $ lift $ runStateT s state {_instructions = mempty}
  put state' {_instructions = _instructions state}
  pure (a, toList $ _instructions state')

emit :: Assembly.Instruction Assembly.BasicBlock -> Builder ()
emit instruction =
  modify $ \s -> s {_instructions = _instructions s Tsil.:> instruction}

-------------------------------------------------------------------------------

data Environment v = Environment
  { _context :: Context v
  , _varLocations :: IntMap Var Operand
  }

emptyEnvironment :: Scope.KeyedName -> Environment Void
emptyEnvironment scopeKey =
  Environment
    { _context = Context.empty scopeKey
    , _varLocations = mempty
    }

extend :: Environment v -> Syntax.Type v -> Operand -> Builder (Environment (Succ v))
extend env type_ location =
  Builder $
    lift $ do
      type' <- Evaluation.evaluate (Context.toEnvironment $ _context env) type_
      (context', var) <- Context.extend (_context env) type'
      pure
        Environment
          { _context = context'
          , _varLocations = IntMap.insert var location $ _varLocations env
          }

operandNameSuggestion :: Assembly.Operand -> Assembly.NameSuggestion
operandNameSuggestion operand =
  case operand of
    Assembly.LocalOperand (Assembly.Local _ nameSuggestion) ->
      nameSuggestion
    Assembly.GlobalConstant global _ ->
      Assembly.NameSuggestion $ Assembly.nameText global
    Assembly.GlobalFunction global _ _ ->
      Assembly.NameSuggestion $ Assembly.nameText global
    Assembly.Lit _ ->
      "literal"

data Operand
  = Empty
  | -- | word sized
    Direct !Assembly.Operand
  | Indirect !Assembly.Operand

-------------------------------------------------------------------------------

indexOperand :: Index v -> Environment v -> Operand
indexOperand index env = do
  let var =
        Context.lookupIndexVar index $ _context env
  fromMaybe (panic "ClosureConvertedToAssembly.indexOperand") $
    IntMap.lookup var $ _varLocations env

globalConstantOperand :: Name.Lifted -> Builder Operand
globalConstantOperand name = do
  maybeSignature <- fetch $ Query.ClosureConvertedSignature name
  pure $ case maybeSignature of
    Just (Representation.ConstantSignature representation) ->
      Indirect $ Assembly.GlobalConstant name representation
    _ ->
      panic $ "ClosureConvertedToAssembly.globalConstantLocation: global without constant signature " <> show name

stackAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
stackAllocate nameSuggestion size = do
  return_ <- freshLocal nameSuggestion
  emit $ Assembly.StackAllocate return_ size
  pure $ Assembly.LocalOperand return_

saveStack :: Builder Assembly.Operand
saveStack = do
  return_ <- freshLocal "stack"
  emit $ Assembly.SaveStack return_
  pure $ Assembly.LocalOperand return_

restoreStack :: Assembly.Operand -> Builder ()
restoreStack stack =
  emit $ Assembly.RestoreStack stack

globalAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
globalAllocate =
  add

heapAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
heapAllocate nameSuggestion size = do
  return_ <- freshLocal nameSuggestion
  emit $ Assembly.HeapAllocate return_ size
  pure $ Assembly.LocalOperand return_

typeOf :: Environment v -> Syntax.Term v -> Builder Operand
typeOf env term = do
  type_ <- Builder $
    lift $ do
      value <- Evaluation.evaluate (Context.toEnvironment $ _context env) term
      typeValue <- TypeOf.typeOf (_context env) value
      Readback.readback (Context.toEnvironment $ _context env) typeValue
  generateType env type_

sizeOfType :: Operand -> Builder Assembly.Operand
sizeOfType =
  forceDirect

-------------------------------------------------------------------------------

freshLocal :: Assembly.NameSuggestion -> Builder Assembly.Local
freshLocal nameSuggestion = do
  fresh <- gets _fresh
  modify $ \s -> s {_fresh = fresh + 1}
  pure $ Assembly.Local fresh nameSuggestion

copy :: Assembly.Operand -> Operand -> Assembly.Operand -> Builder ()
copy destination source size =
  case source of
    Empty ->
      pure ()
    Indirect indirectSource ->
      emit $ Assembly.Copy destination indirectSource size
    Direct directSource ->
      emit $ Assembly.Store destination directSource

callVoid :: Name.Lifted -> [Assembly.Operand] -> Builder ()
callVoid global args =
  emit $ Assembly.Call Assembly.Void (Assembly.GlobalFunction global Assembly.ReturnsVoid $ length args) args

callDirect :: Assembly.NameSuggestion -> Name.Lifted -> [Assembly.Operand] -> Builder Assembly.Operand
callDirect nameSuggestion global args = do
  result <- freshLocal nameSuggestion
  emit $ Assembly.Call (Assembly.NonVoid result) (Assembly.GlobalFunction global Assembly.Returns $ length args) args
  pure $ Assembly.LocalOperand result

callIndirect :: Name.Lifted -> [Assembly.Operand] -> Assembly.Operand -> Builder ()
callIndirect global args returnLocation =
  callVoid global (returnLocation : args)

load :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
load nameSuggestion pointer = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Load destination pointer
  pure $ Assembly.LocalOperand destination

store :: Assembly.Operand -> Assembly.Operand -> Builder ()
store destination value =
  emit $ Assembly.Store destination value

initGlobal :: Name.Lifted -> Representation -> Assembly.Operand -> Builder ()
initGlobal global representation value =
  emit $ Assembly.InitGlobal global representation value

add :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
add nameSuggestion i1 i2 = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Add destination i1 i2
  pure $ Assembly.LocalOperand destination

sub :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
sub nameSuggestion i1 i2 = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Sub destination i1 i2
  pure $ Assembly.LocalOperand destination

-------------------------------------------------------------------------------

forceIndirect :: Operand -> Builder (Assembly.Operand, Builder ())
forceIndirect operand =
  case operand of
    Empty ->
      pure (Assembly.Lit $ Literal.Integer 0, pure ())
    Direct directOperand -> do
      stack <- saveStack
      operand' <- stackAllocate (operandNameSuggestion directOperand) pointerBytesOperand
      pure (operand', restoreStack stack)
    Indirect indirectOperand ->
      pure (indirectOperand, pure ())

forceDirect :: Operand -> Builder Assembly.Operand
forceDirect operand =
  case operand of
    Empty ->
      pure $ Assembly.Lit $ Literal.Integer 0
    Direct directOperand ->
      pure directOperand
    Indirect indirectOperand ->
      load (operandNameSuggestion indirectOperand) indirectOperand

-------------------------------------------------------------------------------

pointerBytes :: Num a => a
pointerBytes =
  8

pointerBytesOperand :: Assembly.Operand
pointerBytesOperand =
  Assembly.Lit $ Literal.Integer pointerBytes

directTypeOperand :: Assembly.Operand
directTypeOperand =
  pointerBytesOperand

emptyTypeOperand :: Assembly.Operand
emptyTypeOperand =
  Assembly.Lit $ Literal.Integer 0

-------------------------------------------------------------------------------

moduleInitName :: Name.Module -> Name.Lifted
moduleInitName moduleName =
  Name.Lifted (Name.Qualified moduleName "$init") 0

moduleInitedName :: Name.Module -> Name.Lifted
moduleInitedName moduleName =
  Name.Lifted (Name.Qualified moduleName "$inited") 0

initDefinitionName :: Name.Lifted -> Name.Lifted
initDefinitionName (Name.Lifted (Name.Qualified moduleName (Name.Name name)) m) =
  Name.Lifted (Name.Qualified moduleName $ Name.Name $ name <> "$init") m

generateModuleInits :: [Name.Module] -> M (Assembly.Definition Assembly.BasicBlock)
generateModuleInits moduleNames =
  runBuilder $ do
    globalPointer <- freshLocal "globals"
    globalPointer' <- foldM go (Assembly.LocalOperand globalPointer) moduleNames
    instructions <- gets _instructions
    pure $ Assembly.FunctionDefinition [globalPointer] $ Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid globalPointer'
  where
    go globalPointer moduleName =
      callDirect "globals" (moduleInitName moduleName) [globalPointer]

generateModuleInit ::
  Name.Module ->
  [(Name.Lifted, Assembly.Definition Assembly.BasicBlock)] ->
  M [(Name.Lifted, Assembly.Definition Assembly.BasicBlock)]
generateModuleInit moduleName definitions =
  runBuilder $ do
    globalPointer <- freshLocal "globals"
    moduleHeader <- fetch $ Query.ModuleHeader moduleName
    globalPointer' <- foldM initImport (Assembly.LocalOperand globalPointer) $ Module._imports moduleHeader
    globalPointer'' <- foldM initDefinition globalPointer' definitions
    instructions <- gets _instructions
    pure
      [
        ( moduleInitName moduleName
        , Assembly.FunctionDefinition [globalPointer] $ Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid globalPointer''
        )
      ]
  where
    initImport globalPointer import_ =
      callDirect "globals" (moduleInitName $ Module._module import_) [globalPointer]

    initDefinition globalPointer (name, definition) =
      case definition of
        Assembly.KnownConstantDefinition {} ->
          pure globalPointer
        Assembly.ConstantDefinition {} ->
          callDirect "globals" (initDefinitionName name) [globalPointer]
        Assembly.FunctionDefinition {} ->
          pure globalPointer

generateDefinition :: Name.Lifted -> Syntax.Definition -> M (Maybe (Assembly.Definition Assembly.BasicBlock))
generateDefinition name@(Name.Lifted qualifiedName _) definition = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  let env =
        emptyEnvironment $ Scope.KeyedName Scope.Definition qualifiedName
  runBuilder $ do
    case (definition, signature) of
      (Syntax.TypeDeclaration _, _) ->
        pure Nothing
      (Syntax.ConstantDefinition term, Just (Representation.ConstantSignature representation)) ->
        generateGlobal env name representation term
      (Syntax.ConstantDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: ConstantDefinition without ConstantSignature"
      (Syntax.FunctionDefinition tele, Just (Representation.FunctionSignature parameterRepresentations returnRepresentation)) -> do
        Just <$> generateFunction env returnRepresentation tele parameterRepresentations mempty
      (Syntax.FunctionDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: FunctionDefinition without FunctionSignature"
      (Syntax.DataDefinition boxity constructors, Just (Representation.ConstantSignature representation)) -> do
        term <- Builder $ lift $ ClosureConverted.Representation.compileData (Context.toEnvironment $ _context env) boxity constructors
        generateGlobal env name representation term
      (Syntax.DataDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: DataDefinition without ConstantSignature"
      (Syntax.ParameterisedDataDefinition boxity tele, Just (Representation.FunctionSignature parameterRepresentations returnRepresentation)) -> do
        tele' <- Builder $ lift $ ClosureConverted.Representation.compileParameterisedData (Context.toEnvironment $ _context env) boxity tele
        Just <$> generateFunction env returnRepresentation tele' parameterRepresentations mempty
      (Syntax.ParameterisedDataDefinition {}, _) -> do
        panic "ClosureConvertedToAssembly: DataDefinition without ConstantSignature"

generateGlobal :: Environment v -> Name.Lifted -> Representation -> Syntax.Term v -> Builder (Maybe (Assembly.Definition Assembly.BasicBlock))
generateGlobal env name representation term = do
  globalPointer <- freshLocal "globals"
  let globalPointerOperand =
        Assembly.LocalOperand globalPointer
  case generateKnownConstant term of
    Just knownConstant ->
      pure $ Just $ Assembly.KnownConstantDefinition representation knownConstant True
    Nothing ->
      case representation of
        Representation.Empty -> do
          (_, deallocateTerm) <- generateTypedTerm env term $ Direct emptyTypeOperand
          sequence_ deallocateTerm
          instructions <- gets _instructions
          pure $
            Just $
              Assembly.ConstantDefinition
                representation
                [globalPointer]
                (Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid globalPointerOperand)
        Representation.Direct containsHeapPointers -> do
          (result, deallocateTerm) <- generateTypedTerm env term $ Direct directTypeOperand
          directResult <- forceDirect result
          sequence_ deallocateTerm
          initGlobal name representation directResult
          instructions <- gets _instructions
          pure $
            Just $
              Assembly.ConstantDefinition
                representation
                [globalPointer]
                (Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid globalPointerOperand)
        Representation.Indirect containsHeapPointers -> do
          type_ <- typeOf env term
          typeSize <- sizeOfType type_
          globalPointer' <- globalAllocate "globals" globalPointerOperand typeSize
          storeTerm env term globalPointerOperand type_
          initGlobal name representation globalPointerOperand
          instructions <- gets _instructions
          pure $
            Just $
              Assembly.ConstantDefinition
                representation
                [globalPointer]
                (Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid globalPointer')

generateKnownConstant :: Syntax.Term v -> Maybe Literal
generateKnownConstant term =
  case term of
    Syntax.Lit lit ->
      pure lit
    Syntax.Global (Name.Lifted Builtin.EmptyRepresentationName 0) ->
      pure $ Literal.Integer 0
    Syntax.Global (Name.Lifted Builtin.WordRepresentationName 0) ->
      pure $ Literal.Integer 8
    Syntax.Global (Name.Lifted Builtin.IntName 0) ->
      pure $ Literal.Integer 8
    Syntax.Global (Name.Lifted Builtin.TypeName 0) ->
      pure $ Literal.Integer 8
    Syntax.Apply (Name.Lifted Builtin.AddRepresentationName 0) [x, y] -> do
      Literal.Integer x' <- generateKnownConstant x
      Literal.Integer y' <- generateKnownConstant y
      pure $ Literal.Integer $ x' + y'
    Syntax.Apply (Name.Lifted Builtin.MaxRepresentationName 0) [x, y] -> do
      Literal.Integer x' <- generateKnownConstant x
      Literal.Integer y' <- generateKnownConstant y
      pure $ Literal.Integer $ max x' y'
    _ ->
      Nothing

generateFunction ::
  Environment v ->
  Representation ->
  Telescope Name Syntax.Type Syntax.Term v ->
  [Representation] ->
  Tsil Assembly.Local ->
  Builder (Assembly.Definition Assembly.BasicBlock)
generateFunction env returnRepresentation tele parameterRepresentations params =
  case (tele, parameterRepresentations) of
    (Telescope.Empty term, []) ->
      case returnRepresentation of
        Representation.Empty -> do
          (_, deallocateTerm) <- generateTypedTerm env term $ Direct emptyTypeOperand
          sequence_ deallocateTerm
          instructions <- gets _instructions
          pure $
            Assembly.FunctionDefinition
              (toList params)
              (Assembly.BasicBlock (toList instructions) Assembly.Void)
        Representation.Direct _ -> do
          (result, deallocateTerm) <- generateTypedTerm env term $ Direct directTypeOperand
          directResult <- forceDirect result
          sequence_ deallocateTerm
          instructions <- gets _instructions
          pure $
            Assembly.FunctionDefinition
              (toList params)
              (Assembly.BasicBlock (toList instructions) $ Assembly.NonVoid directResult)
        Representation.Indirect _ -> do
          returnLocation <- freshLocal "return_location"
          type_ <- typeOf env term
          storeTerm env term (Assembly.LocalOperand returnLocation) type_
          instructions <- gets _instructions
          pure $
            Assembly.FunctionDefinition
              (returnLocation : toList params)
              (Assembly.BasicBlock (toList instructions) Assembly.Void)
    (Telescope.Extend (Name name) type_ _plicity tele', parameterRepresentation : parameterRepresentations') -> do
      (params', paramOperand) <-
        case parameterRepresentation of
          Representation.Empty ->
            pure (params, Empty)
          Representation.Direct Representation.Doesn'tContainHeapPointers -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> local, Direct $ Assembly.LocalOperand local)
          Representation.Direct Representation.MightContainHeapPointers -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> local, Indirect $ Assembly.LocalOperand local)
          Representation.Indirect _ -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> local, Indirect $ Assembly.LocalOperand local)

      env' <- extend env type_ paramOperand
      generateFunction env' returnRepresentation tele' parameterRepresentations' params'
    _ ->
      panic "ClosureConvertedToAssembly.generateFunction: mismatched function telescope and signature"

-------------------------------------------------------------------------------

generateType :: Environment v -> Syntax.Type v -> Builder Operand
generateType env type_ = do
  (type', maybeDeallocateType) <- generateTypedTerm env type_ $ Direct pointerBytesOperand
  case maybeDeallocateType of
    Nothing ->
      pure type'
    Just deallocateType -> do
      directType <- forceDirect type'
      deallocateType
      pure $ Direct directType

generateTypedTerm :: Environment v -> Syntax.Term v -> Operand -> Builder (Operand, Maybe (Builder ()))
generateTypedTerm env term type_ = do
  let stackAllocateIt = do
        typeSize <- sizeOfType type_
        stack <- saveStack
        termLocation <- stackAllocate "term_location" typeSize
        storeTerm env term termLocation type_
        pure
          ( Indirect termLocation
          , Just $ restoreStack stack
          )

  case term of
    Syntax.Var index ->
      pure (indexOperand index env, Nothing)
    Syntax.Global global -> do
      operand <- globalConstantOperand global
      pure (operand, Nothing)
    Syntax.Con {} ->
      stackAllocateIt -- TODO
    Syntax.Lit lit ->
      pure (Direct $ Assembly.Lit lit, Nothing)
    Syntax.Let _name term' termType body -> do
      termType' <- generateType env termType
      (term'', deallocateTerm) <- generateTypedTerm env term' termType'
      env' <- extend env termType term''
      (result, deallocateBody) <- generateTypedTerm env' body type_
      pure (result, (>>) <$> deallocateBody <*> deallocateTerm)
    Syntax.Function _ ->
      pure (Direct pointerBytesOperand, Nothing)
    Syntax.Apply global arguments -> do
      maybeSignature <- fetch $ Query.ClosureConvertedSignature global
      let (argumentRepresentations, returnRepresentation) =
            case maybeSignature of
              Just (Representation.FunctionSignature argumentRepresentations_ returnRepresentation_) ->
                (argumentRepresentations_, returnRepresentation_)
              _ ->
                panic $ "ClosureConvertedToAssembly: Applying signature-less function " <> show global
      case returnRepresentation of
        Representation.Empty -> do
          (arguments', deallocateArguments) <- generateArguments env $ zip arguments argumentRepresentations
          callVoid global arguments'
          deallocateArguments
          pure (Empty, Nothing)
        Representation.Direct containsHeapPointers -> do
          (arguments', deallocateArguments) <- generateArguments env $ zip arguments argumentRepresentations
          result <- callDirect "call_result" global arguments'
          deallocateArguments
          pure (Direct result, Nothing)
        Representation.Indirect containsHeapPointers ->
          stackAllocateIt
    Syntax.Pi {} ->
      pure (Direct pointerBytesOperand, Nothing)
    Syntax.Closure {} ->
      stackAllocateIt
    Syntax.ApplyClosure {} ->
      stackAllocateIt
    Syntax.Case {} ->
      stackAllocateIt

storeTerm ::
  Environment v ->
  Syntax.Term v ->
  Assembly.Operand ->
  Operand ->
  Builder ()
storeTerm env term returnLocation returnType =
  case term of
    Syntax.Var index -> do
      let varOperand =
            indexOperand index env
      returnTypeSize <- sizeOfType returnType
      copy returnLocation varOperand returnTypeSize
    Syntax.Global global -> do
      operand <- globalConstantOperand global
      returnTypeSize <- sizeOfType returnType
      copy returnLocation operand returnTypeSize
    Syntax.Con con@(Name.QualifiedConstructor typeName _) params args -> do
      maybeTag <- fetch $ Query.ConstructorTag con
      let tagArgs =
            case maybeTag of
              Nothing ->
                args
              Just tag ->
                Syntax.Lit (Literal.Integer $ fromIntegral tag) : args

          go location arg = do
            argType <- typeOf env arg
            storeTerm env arg location argType
            argTypeSize <- sizeOfType argType
            add "argument_offset" location argTypeSize

      boxity <- fetchBoxity typeName
      case boxity of
        Unboxed ->
          foldM_ go returnLocation tagArgs
        Boxed -> do
          size <- boxedConstructorSize env con params
          heapLocation <- heapAllocate "constructor_heap_object" size
          foldM_ go heapLocation tagArgs
          store returnLocation heapLocation
    Syntax.Lit lit ->
      store returnLocation (Assembly.Lit lit)
    Syntax.Let _name term' type_ body -> do
      type' <- generateType env type_
      (term'', deallocateTerm) <- generateTypedTerm env term' type'
      env' <- extend env type_ term''
      storeTerm env' body returnLocation returnType
      sequence_ deallocateTerm
    Syntax.Function _ ->
      store returnLocation pointerBytesOperand
    Syntax.Apply global arguments -> do
      maybeSignature <- fetch $ Query.ClosureConvertedSignature global
      let (argumentRepresentations, returnRepresentation) =
            case maybeSignature of
              Just (Representation.FunctionSignature argumentRepresentations_ returnRepresentation_) ->
                (argumentRepresentations_, returnRepresentation_)
              _ ->
                panic $ "ClosureConvertedToAssembly: Applying signature-less function " <> show global
      (arguments', deallocateArguments) <- generateArguments env (zip arguments argumentRepresentations)
      case returnRepresentation of
        Representation.Empty ->
          callVoid global arguments'
        Representation.Direct containsHeapPointers -> do
          result <- callDirect "call_result" global arguments'
          store returnLocation result
        Representation.Indirect containsHeapPointers -> do
          callIndirect global arguments' returnLocation
      deallocateArguments
    Syntax.Pi {} ->
      store returnLocation pointerBytesOperand
    Syntax.Closure {} ->
      panic "st c" -- TODO
    Syntax.ApplyClosure {} ->
      panic $ "st ac " <> show term -- TODO
    Syntax.Case {} ->
      panic "st case" -- TODO

generateArguments :: Environment v -> [(Syntax.Term v, Representation)] -> Builder ([Assembly.Operand], Builder ())
generateArguments env arguments = do
  (argumentGenerators, outerDeallocators) <- unzip <$> mapM (uncurry $ generateArgument env) arguments
  (arguments', innerDeallocators) <- unzip <$> sequence argumentGenerators
  pure
    ( concat arguments'
    , do
        sequence_ $ reverse innerDeallocators
        sequence_ $ reverse outerDeallocators
    )

generateArgument :: Environment v -> Syntax.Term v -> Representation -> Builder (Builder ([Assembly.Operand], Builder ()), Builder ())
generateArgument env term representation =
  case representation of
    Representation.Empty -> do
      (_, deallocateTerm) <- generateTypedTerm env term $ Direct emptyTypeOperand
      pure
        ( pure ([], pure ())
        , sequence_ deallocateTerm
        )
    Representation.Direct containsHeapPointers -> do
      (term', deallocateTerm) <- generateTypedTerm env term $ Direct directTypeOperand
      pure
        ( do
            directTerm <- forceDirect term'
            pure ([directTerm], pure ())
        , sequence_ deallocateTerm
        )
    Representation.Indirect containsHeapPointers -> do
      type_ <- typeOf env term
      (termOperand, deallocateTermOperand) <- generateTypedTerm env term type_
      pure
        ( do
            (termLocation, deallocateTerm) <- forceIndirect termOperand
            pure ([termLocation], deallocateTerm)
        , sequence_ deallocateTermOperand
        )

-------------------------------------------------------------------------------

fetchBoxity :: MonadFetch Query m => Name.Qualified -> m Boxity
fetchBoxity name = do
  maybeDef <- fetch $ Query.ElaboratedDefinition name
  case maybeDef of
    Just (Core.Syntax.DataDefinition boxity _, _) ->
      pure boxity
    _ ->
      panic "ClosureConvertedToAssembly.fetchBoxity"

boxedConstructorSize ::
  Environment v ->
  Name.QualifiedConstructor ->
  [Syntax.Term v] ->
  m Assembly.Operand
boxedConstructorSize =
  panic "bcs"
