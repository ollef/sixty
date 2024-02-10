{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module ClosureConvertedToAssembly where

import qualified Assembly
import Boxity
import qualified Builtin
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Domain as Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Representation
import qualified ClosureConverted.Syntax as Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import Control.Monad.Fail
import Data.EnumMap (EnumMap)
import qualified Data.EnumMap as EnumMap
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index
import Literal (Literal)
import qualified Literal
import qualified Module
import Monad
import Name (Name (Name))
import qualified Name
import Protolude hiding (local, moduleName, state, typeOf)
import Query (Query)
import qualified Query
import Representation (Representation)
import qualified Representation
import Rock
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

newtype Builder a = Builder (StateT BuilderState M a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFetch Query, MonadState BuilderState)

instance MonadFail Builder where
  fail = panic . toS

data BuilderState = BuilderState
  { fresh :: !Int
  , instructions :: Tsil Assembly.Instruction
  }

runBuilder :: Builder a -> M a
runBuilder (Builder s) =
  evalStateT
    s
    BuilderState
      { fresh = 3
      , instructions = mempty
      }

subBuilder :: Builder a -> Builder (a, [Assembly.Instruction])
subBuilder (Builder s) = do
  state <- get
  (a, state') <- Builder $ lift $ runStateT s state {instructions = mempty}
  put state' {instructions = state.instructions}
  pure (a, toList state'.instructions)

emit :: Assembly.Instruction -> Builder ()
emit instruction =
  modify \s -> s {instructions = s.instructions Tsil.:> instruction}

tagBytes :: (Num a) => a
tagBytes = wordBytes

wordBytes :: (Num a) => a
wordBytes = 8

-------------------------------------------------------------------------------

data Environment v = Environment
  { context :: Context v
  , varLocations :: EnumMap Var Operand
  }

emptyEnvironment :: Environment Void
emptyEnvironment =
  Environment
    { context = Context.empty
    , varLocations = mempty
    }

extend :: Environment v -> Syntax.Type v -> Operand -> Builder (Environment (Succ v))
extend env type_ location =
  Builder $
    lift do
      type' <- Evaluation.evaluate (Context.toEnvironment env.context) type_
      (context', var) <- Context.extend env.context type'
      pure
        Environment
          { context = context'
          , varLocations = EnumMap.insert var location env.varLocations
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
    Assembly.StructOperand _ ->
      "struct"

data Operand
  = Empty
  | -- | word sized
    Direct !Assembly.Operand
  | Indirect !Assembly.Operand

-------------------------------------------------------------------------------

indexOperand :: Index v -> Environment v -> Operand
indexOperand index env = do
  let var =
        Context.lookupIndexVar index env.context
  fromMaybe (panic "ClosureConvertedToAssembly.indexOperand") $
    EnumMap.lookup var env.varLocations

globalConstantOperand :: Name.Lifted -> Builder Operand
globalConstantOperand name = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  pure case signature of
    Representation.ConstantSignature representation ->
      Indirect $
        Assembly.GlobalConstant name case representation of
          Representation.Empty -> Assembly.WordPointer
          Representation.Direct -> Assembly.Word
          Representation.Indirect -> Assembly.WordPointer
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

heapAllocate :: Assembly.NameSuggestion -> Word8 -> Assembly.Operand -> Builder Assembly.Operand
heapAllocate nameSuggestion constructorTag size = do
  destination <- freshLocal nameSuggestion
  emit Assembly.HeapAllocate {destination, constructorTag, size}
  pure $ Assembly.LocalOperand destination

extractHeapPointer :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
extractHeapPointer nameSuggestion location = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.ExtractHeapPointer destination location
  pure $ Assembly.LocalOperand destination

extractHeapPointerConstructorTag :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
extractHeapPointerConstructorTag nameSuggestion location = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.ExtractHeapPointerConstructorTag destination location
  pure $ Assembly.LocalOperand destination

typeOf :: Environment v -> Syntax.Term v -> Builder (Operand, Representation)
typeOf env term = do
  (type_, typeRepresentation) <- Builder $
    lift do
      value <- Evaluation.evaluate (Context.toEnvironment env.context) term
      typeValue <- TypeOf.typeOf env.context value
      typeRepresentation <- ClosureConverted.Representation.typeRepresentation (Context.toEnvironment env.context) typeValue
      type_ <- Readback.readback (Context.toEnvironment env.context) typeValue
      pure (type_, typeRepresentation)
  typeOperand <- generateType env type_
  pure (typeOperand, typeRepresentation)

sizeOfType :: Operand -> Builder Assembly.Operand
sizeOfType =
  forceDirect

switch
  :: Assembly.Return (Assembly.Type, Assembly.NameSuggestion)
  -> Assembly.Operand
  -> [(Integer, Builder (Assembly.Return Assembly.Operand))]
  -> Builder (Assembly.Return Assembly.Operand)
  -> Builder (Assembly.Return Assembly.Operand)
switch returnType scrutinee branches defaultBranch = do
  (defaultReturn, defaultInstructions) <- subBuilder defaultBranch
  branches' <- forM branches \(i, branch) -> do
    (branchReturn, branchInstructions) <- subBuilder branch
    pure (i, Assembly.BasicBlock branchInstructions branchReturn)
  case returnType of
    Assembly.Void -> do
      emit $ Assembly.Switch Assembly.Void scrutinee branches' $ Assembly.BasicBlock defaultInstructions defaultReturn
      pure Assembly.Void
    Assembly.Return (type_, nameSuggestion) -> do
      resultLocal <- freshLocal nameSuggestion
      emit $ Assembly.Switch (Assembly.Return (type_, resultLocal)) scrutinee branches' $ Assembly.BasicBlock defaultInstructions defaultReturn
      pure $ Assembly.Return $ Assembly.LocalOperand resultLocal

-------------------------------------------------------------------------------

freshLocal :: Assembly.NameSuggestion -> Builder Assembly.Local
freshLocal nameSuggestion = do
  fresh <- gets (.fresh)
  modify \s -> s {fresh = fresh + 1}
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

callVoid :: Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Builder ()
callVoid global args =
  emit $ Assembly.Call Assembly.Void (Assembly.GlobalFunction global Assembly.Void $ fst <$> args) args

callDirect :: Assembly.NameSuggestion -> Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Builder Assembly.Operand
callDirect nameSuggestion global args = do
  result <- freshLocal nameSuggestion
  emit $
    Assembly.Call
      (Assembly.Return (Assembly.Word, result))
      (Assembly.GlobalFunction global (Assembly.Return Assembly.Word) $ fst <$> args)
      args
  pure $ Assembly.LocalOperand result

callIndirect :: Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Assembly.Operand -> Builder ()
callIndirect global args returnLocation =
  callVoid global ((Assembly.WordPointer, returnLocation) : args)

load :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
load nameSuggestion pointer = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Load destination pointer
  pure $ Assembly.LocalOperand destination

store :: Assembly.Operand -> Assembly.Operand -> Builder ()
store destination value =
  emit $ Assembly.Store destination value

initGlobal :: Name.Lifted -> Assembly.Type -> Assembly.Operand -> Builder ()
initGlobal global type_ value =
  emit $ Assembly.InitGlobal global type_ value

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

mul :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
mul nameSuggestion i1 i2 = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Mul destination i1 i2
  pure $ Assembly.LocalOperand destination

addPointer :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
addPointer nameSuggestion i1 i2 = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.AddPointer destination i1 i2
  pure $ Assembly.LocalOperand destination

extractValue :: Assembly.NameSuggestion -> Assembly.Operand -> Int -> Builder Assembly.Operand
extractValue nameSuggestion struct index = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.ExtractValue destination struct index
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
      store operand' directOperand
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

pointerBytes :: (Num a) => a
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

generateModuleInits :: [Name.Module] -> M Assembly.Definition
generateModuleInits moduleNames =
  runBuilder do
    forM_ moduleNames \moduleName ->
      callVoid (moduleInitName moduleName) []
    instructions <- gets (.instructions)
    pure $
      Assembly.FunctionDefinition Assembly.Void [] $
        Assembly.BasicBlock (toList instructions) Assembly.Void

generateModuleInit
  :: Name.Module
  -> [(Name.Lifted, Assembly.Definition)]
  -> M [(Name.Lifted, Assembly.Definition)]
generateModuleInit moduleName definitions =
  runBuilder do
    inited <- load "inited" $ Assembly.GlobalConstant initedName Assembly.Word
    Assembly.Void <-
      switch
        Assembly.Void
        inited
        [
          ( 0
          , do
              initGlobal initedName Assembly.Word $ Assembly.Lit $ Literal.Integer 1
              moduleHeader <- fetch $ Query.ModuleHeader moduleName
              forM_ moduleHeader.imports \import_ ->
                callVoid (moduleInitName import_.module_) []
              forM_ definitions initDefinition
              pure Assembly.Void
          )
        ]
        $ pure Assembly.Void
    instructions <- gets (.instructions)
    pure
      [
        ( moduleInitName moduleName
        , Assembly.FunctionDefinition
            Assembly.Void
            []
            (Assembly.BasicBlock (toList instructions) Assembly.Void)
        )
      ,
        ( initedName
        , Assembly.KnownConstantDefinition Assembly.Word (Literal.Integer 0) False
        )
      ]
  where
    initedName = moduleInitedName moduleName
    initDefinition (name, definition) =
      case definition of
        Assembly.KnownConstantDefinition {} ->
          pure ()
        Assembly.ConstantDefinition {} ->
          callVoid (initDefinitionName name) []
        Assembly.FunctionDefinition {} ->
          pure ()

generateDefinition :: Name.Lifted -> Syntax.Definition -> M (Maybe Assembly.Definition)
generateDefinition name@(Name.Lifted qualifiedName _) definition = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  let env = emptyEnvironment
  runBuilder do
    case (definition, signature) of
      (Syntax.TypeDeclaration _, _) ->
        pure Nothing
      (Syntax.ConstantDefinition term, Representation.ConstantSignature representation) ->
        Just <$> generateGlobal env name representation term
      (Syntax.ConstantDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: ConstantDefinition without ConstantSignature"
      (Syntax.FunctionDefinition tele, Representation.FunctionSignature parameterRepresentations returnRepresentation) -> do
        Just <$> generateFunction env returnRepresentation tele parameterRepresentations mempty
      (Syntax.FunctionDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: FunctionDefinition without FunctionSignature"
      (Syntax.DataDefinition _ constructors, Representation.ConstantSignature representation) -> do
        term <- Builder $ lift $ ClosureConverted.Representation.compileData (Context.toEnvironment env.context) qualifiedName constructors
        Just <$> generateGlobal env name representation term
      (Syntax.DataDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: DataDefinition without ConstantSignature"
      (Syntax.ParameterisedDataDefinition _ tele, Representation.FunctionSignature parameterRepresentations returnRepresentation) -> do
        tele' <- Builder $ lift $ ClosureConverted.Representation.compileParameterisedData (Context.toEnvironment env.context) qualifiedName tele
        Just <$> generateFunction env returnRepresentation tele' parameterRepresentations mempty
      (Syntax.ParameterisedDataDefinition {}, _) -> do
        panic "ClosureConvertedToAssembly: DataDefinition without ConstantSignature"

generateGlobal :: Environment v -> Name.Lifted -> Representation -> Syntax.Term v -> Builder Assembly.Definition
generateGlobal env name representation term = do
  case generateKnownConstant term of
    Just knownConstant ->
      pure $ Assembly.KnownConstantDefinition Assembly.Word knownConstant True
    Nothing ->
      case representation of
        Representation.Empty -> makeConstantDefinition Assembly.WordPointer do
          (_, deallocateTerm) <- generateTypedTerm env term (Direct emptyTypeOperand) representation
          sequence_ deallocateTerm
        Representation.Direct -> makeConstantDefinition Assembly.Word do
          (result, deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) representation
          directResult <- forceDirect result
          sequence_ deallocateTerm
          initGlobal name Assembly.Word directResult
        Representation.Indirect ->
          makeConstantDefinition Assembly.WordPointer do
            (type_, _representation) <- typeOf env term
            typeSize <- sizeOfType type_
            taggedPointer <- heapAllocate "tagged_global_pointer" 0 typeSize
            pointer <- extractHeapPointer "global_pointer" taggedPointer
            storeTerm env term pointer type_
            initGlobal name Assembly.WordPointer pointer

makeConstantDefinition
  :: Assembly.Type
  -> Builder ()
  -> Builder Assembly.Definition
makeConstantDefinition type_ m = do
  m
  instructions <- gets (.instructions)
  pure $
    Assembly.ConstantDefinition type_ Assembly.Void [] $
      Assembly.BasicBlock (toList instructions) Assembly.Void

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

generateFunction
  :: Environment v
  -> Representation
  -> Telescope Name Syntax.Type Syntax.Term v
  -> [Representation]
  -> Tsil (Assembly.Type, Assembly.Local)
  -> Builder Assembly.Definition
generateFunction env returnRepresentation tele parameterRepresentations params =
  case (tele, parameterRepresentations) of
    (Telescope.Empty term, []) ->
      case returnRepresentation of
        Representation.Empty ->
          makeFunctionDefinition Assembly.Void (toList params) do
            (_, deallocateTerm) <- generateTypedTerm env term (Direct emptyTypeOperand) returnRepresentation
            sequence_ deallocateTerm
            pure Assembly.Void
        Representation.Direct ->
          makeFunctionDefinition (Assembly.Return Assembly.Word) (toList params) do
            (result, deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) returnRepresentation
            directResult <- forceDirect result
            sequence_ deallocateTerm
            pure $ Assembly.Return directResult
        Representation.Indirect -> do
          returnLocation <- freshLocal "return_location"
          makeFunctionDefinition Assembly.Void ((Assembly.WordPointer, returnLocation) : toList params) do
            (type_, _representation) <- typeOf env term
            storeTerm env term (Assembly.LocalOperand returnLocation) type_
            pure Assembly.Void
    (Telescope.Extend (Name name) type_ _plicity tele', parameterRepresentation : parameterRepresentations') -> do
      (params', paramOperand) <-
        case parameterRepresentation of
          Representation.Empty ->
            pure (params, Empty)
          Representation.Direct -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> (Assembly.Word, local), Direct $ Assembly.LocalOperand local)
          Representation.Indirect -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> (Assembly.WordPointer, local), Indirect $ Assembly.LocalOperand local)

      env' <- extend env type_ paramOperand
      generateFunction env' returnRepresentation tele' parameterRepresentations' params'
    _ ->
      panic "ClosureConvertedToAssembly.generateFunction: mismatched function telescope and signature"

makeFunctionDefinition
  :: Assembly.Return Assembly.Type
  -> [(Assembly.Type, Assembly.Local)]
  -> Builder (Assembly.Return Assembly.Operand)
  -> Builder Assembly.Definition
makeFunctionDefinition returnType parameters m = do
  returnOperand <- m
  instructions <- gets (.instructions)
  pure $ Assembly.FunctionDefinition returnType parameters $ Assembly.BasicBlock (toList instructions) returnOperand

-------------------------------------------------------------------------------

generateType :: Environment v -> Syntax.Type v -> Builder Operand
generateType env type_ = do
  (type', maybeDeallocateType) <- generateTypedTerm env type_ (Direct pointerBytesOperand) Representation.Direct
  case maybeDeallocateType of
    Nothing ->
      pure type'
    Just deallocateType -> do
      directType <- forceDirect type'
      deallocateType
      pure $ Direct directType

generateTypedTerm :: Environment v -> Syntax.Term v -> Operand -> Representation -> Builder (Operand, Maybe (Builder ()))
generateTypedTerm env term type_ representation = do
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
    Syntax.Lit (Literal.Integer integer) ->
      pure (Direct $ Assembly.Lit $ Literal.Integer $ shiftL integer 1, Nothing)
    Syntax.Let _name term' termType body -> do
      typeValue <- Builder $ lift $ Evaluation.evaluate (Context.toEnvironment env.context) termType
      typeRepresentation <- Builder $ lift $ ClosureConverted.Representation.typeRepresentation (Context.toEnvironment env.context) typeValue
      termType' <- generateType env termType
      (term'', deallocateTerm) <- generateTypedTerm env term' termType' typeRepresentation
      env' <- extend env termType term''
      (result, deallocateBody) <- generateTypedTerm env' body type_ representation
      pure (result, (>>) <$> deallocateBody <*> deallocateTerm)
    Syntax.Function _ ->
      pure (Direct pointerBytesOperand, Nothing)
    Syntax.Apply global arguments -> do
      signature <- fetch $ Query.ClosureConvertedSignature global
      let (argumentRepresentations, returnRepresentation) =
            case signature of
              Representation.FunctionSignature argumentRepresentations_ returnRepresentation_ ->
                (argumentRepresentations_, returnRepresentation_)
              _ ->
                panic $ "ClosureConvertedToAssembly: Applying signature-less function " <> show global
      case returnRepresentation of
        Representation.Empty -> do
          (arguments', deallocateArguments) <- generateArguments env $ zip arguments argumentRepresentations
          callVoid global arguments'
          deallocateArguments
          pure (Empty, Nothing)
        Representation.Direct -> do
          (arguments', deallocateArguments) <- generateArguments env $ zip arguments argumentRepresentations
          result <- callDirect "call_result" global arguments'
          deallocateArguments
          pure (Direct result, Nothing)
        Representation.Indirect ->
          stackAllocateIt
    Syntax.Pi {} ->
      pure (Direct pointerBytesOperand, Nothing)
    Syntax.Closure {} ->
      stackAllocateIt
    Syntax.ApplyClosure {} ->
      stackAllocateIt
    Syntax.Case {} ->
      stackAllocateIt

storeTerm
  :: Environment v
  -> Syntax.Term v
  -> Assembly.Operand
  -> Operand
  -> Builder ()
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
    Syntax.Con con params args -> do
      (boxity, maybeTag) <- fetch $ Query.ConstructorRepresentation con
      let tagArgs =
            case maybeTag of
              Nothing ->
                args
              Just tag ->
                Syntax.Lit (Literal.Integer $ fromIntegral tag) : args

      case boxity of
        Unboxed -> do
          let go constructLocation arg = do
                location <- constructLocation
                (argType, _argRepresentation) <- typeOf env arg
                storeTerm env arg location argType
                pure do
                  argTypeSize <- sizeOfType argType
                  addPointer "constructor_argument_offset" location argTypeSize
          foldM_ go (pure returnLocation) tagArgs
        Boxed -> do
          let go constructOffset arg = do
                offset <- constructOffset
                (argType, argRepresentation) <- typeOf env arg
                argTypeSize <- sizeOfType argType
                (arg', deallocateArg) <- generateTypedTerm env arg argType argRepresentation
                taggedPointer <- load "tagged_heap_pointer" returnLocation
                basePointer <- extractHeapPointer "boxed_constructor_base" taggedPointer
                argPointer <- addPointer "boxed_constructor_arg" basePointer offset
                copy argPointer arg' argTypeSize
                sequence_ deallocateArg
                pure $ add "constructor_argument_offset" offset argTypeSize
          typeValue <- Builder $ lift $ boxedConstructorSize (Context.toEnvironment env.context) con params args
          type_ <- Builder $ lift $ Readback.readback (Context.toEnvironment env.context) typeValue
          type' <- generateType env type_
          size <- sizeOfType type'
          case maybeTag of
            Nothing -> do
              heapLocation <- heapAllocate "constructor_heap_object" 0 size
              store returnLocation heapLocation
              foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) args
            Just tag
              | tag < 0xFF -> do
                  heapLocation <- heapAllocate "constructor_heap_object" (fromIntegral tag) size
                  store returnLocation heapLocation
                  foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) args
              | otherwise -> do
                  sizeWithTag <- add "size_with_tag" size $ Assembly.Lit $ Literal.Integer tagBytes
                  heapLocation <- heapAllocate "constructor_heap_object" 0xFF sizeWithTag
                  store returnLocation heapLocation
                  foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) tagArgs
    Syntax.Lit (Literal.Integer integer) ->
      store returnLocation $ Assembly.Lit $ Literal.Integer $ shiftL integer 1
    Syntax.Let _name term' type_ body -> do
      typeValue <- Builder $ lift $ Evaluation.evaluate (Context.toEnvironment env.context) type_
      typeRepresentation <- Builder $ lift $ ClosureConverted.Representation.typeRepresentation (Context.toEnvironment env.context) typeValue
      type' <- generateType env type_
      (term'', deallocateTerm) <- generateTypedTerm env term' type' typeRepresentation
      env' <- extend env type_ term''
      storeTerm env' body returnLocation returnType
      sequence_ deallocateTerm
    Syntax.Function _ ->
      store returnLocation pointerBytesOperand
    Syntax.Apply global arguments -> do
      signature <- fetch $ Query.ClosureConvertedSignature global
      let (argumentRepresentations, returnRepresentation) =
            case signature of
              Representation.FunctionSignature argumentRepresentations_ returnRepresentation_ ->
                (argumentRepresentations_, returnRepresentation_)
              _ ->
                panic $ "ClosureConvertedToAssembly: Applying signature-less function " <> show global
      (arguments', deallocateArguments) <- generateArguments env (zip arguments argumentRepresentations)
      case returnRepresentation of
        Representation.Empty ->
          callVoid global arguments'
        Representation.Direct -> do
          result <- callDirect "call_result" global arguments'
          store returnLocation result
        Representation.Indirect -> do
          callIndirect global arguments' returnLocation
      deallocateArguments
    Syntax.Pi {} ->
      store returnLocation pointerBytesOperand
    Syntax.Closure {} ->
      panic "st c" -- TODO
    Syntax.ApplyClosure {} ->
      panic $ "st ac " <> show term -- TODO
    Syntax.Case scrutinee branches maybeDefaultBranch -> do
      let defaultBranch =
            fromMaybe
              (Syntax.Apply (Name.Lifted Builtin.UnknownName 0) [Syntax.Global $ Name.Lifted Builtin.UnitName 0])
              maybeDefaultBranch
      (scrutineeType, scrutineeRepresentation) <- typeOf env scrutinee
      (scrutinee', deallocateScrutinee) <- generateTypedTerm env scrutinee scrutineeType scrutineeRepresentation
      branches' <- ClosureConverted.Representation.compileBranches branches
      case branches' of
        ClosureConverted.Representation.TaggedConstructorBranches Unboxed constructorBranches -> do
          (scrutinee'', deallocateScrutinee') <- forceIndirect scrutinee'
          let firstConstructorFieldBuilder nameSuggestion =
                addPointer nameSuggestion scrutinee'' $ Assembly.Lit $ Literal.Integer tagBytes
          constructorTag <- load "constructor_tag" scrutinee''
          void $
            switch
              Assembly.Void
              constructorTag
              [ ( fromIntegral $ shiftL branchTag 1
                , do
                    storeUnboxedBranch env firstConstructorFieldBuilder branch returnLocation returnType
                    deallocateScrutinee'
                    sequence_ deallocateScrutinee
                    pure Assembly.Void
                )
              | (branchTag, branch) <- constructorBranches
              ]
              ( do
                  deallocateScrutinee'
                  sequence_ deallocateScrutinee
                  storeTerm env defaultBranch returnLocation returnType
                  pure Assembly.Void
              )
        ClosureConverted.Representation.TaggedConstructorBranches Boxed constructorBranches -> do
          scrutinee'' <- forceDirect scrutinee'
          sequence_ deallocateScrutinee
          let constructorBasePointerBuilder = extractHeapPointer "boxed_constructor_pointer" scrutinee''
              firstConstructorFieldOffsetBuilder _ = pure $ Assembly.Lit $ Literal.Integer 0
          constructorTag <- extractHeapPointerConstructorTag "heap_scrutinee_tag" scrutinee''
          void $
            switch
              Assembly.Void
              constructorTag
              [ ( fromIntegral branchTag
                , do
                    storeBoxedBranch env constructorBasePointerBuilder firstConstructorFieldOffsetBuilder branch returnLocation returnType
                    pure Assembly.Void
                )
              | (branchTag, branch) <- constructorBranches
              ]
              ( do
                  storeTerm env defaultBranch returnLocation returnType
                  pure Assembly.Void
              )
        ClosureConverted.Representation.UntaggedConstructorBranch Unboxed branch -> do
          (scrutinee'', deallocateScrutinee') <- forceIndirect scrutinee'
          storeUnboxedBranch env (const $ pure scrutinee'') branch returnLocation returnType
          deallocateScrutinee'
          sequence_ deallocateScrutinee
        ClosureConverted.Representation.UntaggedConstructorBranch Boxed branch -> do
          scrutinee'' <- forceDirect scrutinee'
          sequence_ deallocateScrutinee
          let constructorBasePointerBuilder = extractHeapPointer "boxed_constructor_pointer" scrutinee''
              firstConstructorFieldOffsetBuilder _ = pure $ Assembly.Lit $ Literal.Integer 0
          storeBoxedBranch env constructorBasePointerBuilder firstConstructorFieldOffsetBuilder branch returnLocation returnType
        ClosureConverted.Representation.LiteralBranches literalBranches -> do
          directScrutinee <- forceDirect scrutinee'
          sequence_ deallocateScrutinee
          void $
            switch
              Assembly.Void
              directScrutinee
              [ ( shiftL integer 1
                , do
                    storeTerm env branch returnLocation returnType
                    pure Assembly.Void
                )
              | (Literal.Integer integer, branch) <- OrderedHashMap.toList literalBranches
              ]
              ( do
                  storeTerm env defaultBranch returnLocation returnType
                  pure Assembly.Void
              )

storeUnboxedBranch
  :: Environment v
  -> (Assembly.NameSuggestion -> Builder Assembly.Operand)
  -> Telescope Name Syntax.Type Syntax.Term v
  -> Assembly.Operand
  -> Operand
  -> Builder ()
storeUnboxedBranch env constructorFieldBuilder tele returnLocation returnType =
  case tele of
    Telescope.Extend (Name name) type_ _plicity tele' -> do
      constructorField <- constructorFieldBuilder $ Assembly.NameSuggestion name
      let nextConstructorFieldBuilder nameSuggestion = do
            type' <- generateType env type_
            typeSize <- sizeOfType type'
            addPointer nameSuggestion constructorField typeSize
      env' <- extend env type_ $ Indirect constructorField
      storeUnboxedBranch env' nextConstructorFieldBuilder tele' returnLocation returnType
    Telescope.Empty branch ->
      storeTerm env branch returnLocation returnType

storeBoxedBranch
  :: Environment v
  -> Builder Assembly.Operand
  -> (Assembly.NameSuggestion -> Builder Assembly.Operand)
  -> Telescope Name Syntax.Type Syntax.Term v
  -> Assembly.Operand
  -> Operand
  -> Builder ()
storeBoxedBranch env constructorBasePointerBuilder constructorFieldOffsetBuilder tele returnLocation returnType =
  case tele of
    Telescope.Extend (Name name) type_ _plicity tele' -> do
      constructorFieldOffset <- constructorFieldOffsetBuilder $ Assembly.NameSuggestion $ name <> "_offset"
      type' <- generateType env type_
      typeSize <- sizeOfType type'
      stack <- saveStack
      stackConstructorField <- stackAllocate (Assembly.NameSuggestion $ name <> "_stack") typeSize
      constructorBasePointer <- constructorBasePointerBuilder
      constructorField <- addPointer (Assembly.NameSuggestion name) constructorBasePointer constructorFieldOffset
      copy stackConstructorField (Indirect constructorField) typeSize
      let nextConstructorFieldOffsetBuilder nameSuggestion =
            add nameSuggestion constructorFieldOffset typeSize
      env' <- extend env type_ $ Indirect stackConstructorField
      storeBoxedBranch env' constructorBasePointerBuilder nextConstructorFieldOffsetBuilder tele' returnLocation returnType
      restoreStack stack
    Telescope.Empty branch ->
      storeTerm env branch returnLocation returnType

generateArguments :: Environment v -> [(Syntax.Term v, Representation)] -> Builder ([(Assembly.Type, Assembly.Operand)], Builder ())
generateArguments env arguments = do
  (argumentGenerators, outerDeallocators) <- mapAndUnzipM (uncurry $ generateArgument env) arguments
  (arguments', innerDeallocators) <- unzip <$> sequence argumentGenerators
  pure
    ( concat arguments'
    , do
        sequence_ $ reverse innerDeallocators
        sequence_ $ reverse outerDeallocators
    )

generateArgument :: Environment v -> Syntax.Term v -> Representation -> Builder (Builder ([(Assembly.Type, Assembly.Operand)], Builder ()), Builder ())
generateArgument env term representation =
  case representation of
    Representation.Empty -> do
      (_, deallocateTerm) <- generateTypedTerm env term (Direct emptyTypeOperand) representation
      pure
        ( pure ([], pure ())
        , sequence_ deallocateTerm
        )
    Representation.Direct -> do
      (term', deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) representation
      pure
        ( do
            directTerm <- forceDirect term'
            pure ([(Assembly.Word, directTerm)], pure ())
        , sequence_ deallocateTerm
        )
    Representation.Indirect -> do
      (type_, representation_) <- typeOf env term
      (termOperand, deallocateTermOperand) <- generateTypedTerm env term type_ representation_
      pure
        ( do
            (termLocation, deallocateTerm) <- forceIndirect termOperand
            pure ([(Assembly.WordPointer, termLocation)], deallocateTerm)
        , sequence_ deallocateTermOperand
        )

-------------------------------------------------------------------------------

boxedConstructorSize
  :: Domain.Environment v
  -> Name.QualifiedConstructor
  -> [Syntax.Term v]
  -> [Syntax.Term v]
  -> M Domain.Value
boxedConstructorSize env con params args = do
  tele <- fetch $ Query.ClosureConvertedConstructorType con
  params' <- mapM (Evaluation.evaluate env) params
  args' <- mapM (Evaluation.evaluate env) args
  maybeResult <- Evaluation.applyTelescope env (Telescope.fromVoid tele) params' \env' type_ -> do
    type' <- Evaluation.evaluate env' type_
    size <- ClosureConverted.Representation.compileBoxedConstructorFields env' type' args'
    Evaluation.evaluate env' size
  case maybeResult of
    Nothing -> panic "boxedConstructorSize: Data params length mismatch"
    Just result -> pure result
