{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

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
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
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

instance MonadFail Builder where
  fail = panic . toS

data BuilderState = BuilderState
  { _fresh :: !Int
  , _instructions :: Tsil Assembly.Instruction
  , _shadowStack :: !Assembly.Local
  , _heapPointer :: !Assembly.Operand
  , _heapLimit :: !Assembly.Operand
  , _nextShadowStackSlot :: !Int
  , _shadowStackSlotCount :: !Int
  }

runBuilder :: Builder a -> M a
runBuilder (Builder s) =
  evalStateT
    s
    BuilderState
      { _fresh = 3
      , _instructions = mempty
      , _shadowStack = Assembly.Local 0 "shadow_stack_frame"
      , _heapPointer = Assembly.LocalOperand $ Assembly.Local 1 "heap_pointer"
      , _heapLimit = Assembly.LocalOperand $ Assembly.Local 2 "heap_limit"
      , _nextShadowStackSlot = 0
      , _shadowStackSlotCount = 0
      }

subBuilder :: Builder a -> Builder (a, [Assembly.Instruction])
subBuilder (Builder s) = do
  state <- get
  (a, state') <- Builder $ lift $ runStateT s state {_instructions = mempty}
  put state' {_instructions = _instructions state}
  pure (a, toList $ _instructions state')

emit :: Assembly.Instruction -> Builder ()
emit instruction =
  modify $ \s -> s {_instructions = _instructions s Tsil.:> instruction}

tagBytes :: Num a => a
tagBytes = wordBytes

wordBytes :: Num a => a
wordBytes = 8

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
    Assembly.StructOperand _ ->
      "struct"

data Operand
  = Empty
  | -- | word sized
    Direct !Assembly.Operand
  | Indirect !Assembly.Operand

-------------------------------------------------------------------------------
registerShadowStackSlot :: Assembly.Operand -> Assembly.Operand -> Builder (Builder ())
registerShadowStackSlot size location = do
  (slot, freeSlot) <- getFreeShadowStackSlot
  shadowStack <- gets _shadowStack
  sizeSlot <-
    addPointer
      "size_slot"
      (Assembly.LocalOperand shadowStack)
      (Assembly.Lit $ Literal.Integer $ fromIntegral $ (2 + 2 * slot) * wordBytes)
  store sizeSlot size
  locationSlot <- addPointer "location_slot" sizeSlot $ Assembly.Lit $ Literal.Integer wordBytes
  store locationSlot location
  let unregisterShadowStackSlot = do
        store sizeSlot $ Assembly.Lit $ Literal.Integer 0
        store locationSlot $ Assembly.Lit $ Literal.Integer 0
        freeSlot
  pure unregisterShadowStackSlot

getFreeShadowStackSlot :: Builder (Int, Builder ())
getFreeShadowStackSlot = do
  slot <- gets _nextShadowStackSlot
  let newNextSlot = slot + 1
  modify $ \s ->
    s
      { _nextShadowStackSlot = newNextSlot
      , _shadowStackSlotCount = max newNextSlot $ _shadowStackSlotCount s
      }
  pure
    ( slot
    , modify $ \s ->
        s
          { _nextShadowStackSlot =
              if _nextShadowStackSlot s == newNextSlot
                then slot
                else panic "ClosureConvertedToAssembly.getFreeShadowStackSlot: shadow stack not used FIFO"
          }
    )

shadowStackInitFromGlobals :: Assembly.Local -> Assembly.Local -> Builder [Assembly.Instruction]
shadowStackInitFromGlobals globalBasePointer globalPointer = map snd $
  subBuilder $ do
    slotCount <- gets _shadowStackSlotCount
    shadowStack <- gets _shadowStack
    let slotCount' = slotCount + 1
        globalBasePointerOperand = Assembly.LocalOperand globalBasePointer
        globalPointerOperand = Assembly.LocalOperand globalPointer
        shadowStackSize = Assembly.Lit $ Literal.Integer $ fromIntegral $ (2 + 2 * slotCount') * wordBytes
        shadowStackOperand = Assembly.LocalOperand shadowStack
    emit $ Assembly.StackAllocate shadowStack shadowStackSize
    shadowStackSizeSlot <- addPointer "shadow_stack_frame_size" shadowStackOperand $ Assembly.Lit $ Literal.Integer wordBytes
    store shadowStackSizeSlot $ Assembly.Lit $ Literal.Integer $ fromIntegral slotCount'
    globalsSize <- sub "globals_size" globalPointerOperand globalBasePointerOperand
    globalsSizeSlot <- addPointer "globals_size_shadow_stack_frame_slot" shadowStackSizeSlot $ Assembly.Lit $ Literal.Integer wordBytes
    store globalsSizeSlot globalsSize
    globalsSlot <- addPointer "globals_shadow_stack_frame_slot" globalsSizeSlot $ Assembly.Lit $ Literal.Integer wordBytes
    store globalsSlot globalBasePointerOperand

shadowStackInit :: Builder (Assembly.Local, [Assembly.Instruction])
shadowStackInit =
  subBuilder $ do
    shadowStack <- gets _shadowStack
    slotCount <- gets _shadowStackSlotCount
    case slotCount of
      0 ->
        pure shadowStack
      _ -> do
        shadowStackParameter <- freshLocal "caller_shadow_stack_frame"
        let shadowStackSize = Assembly.Lit $ Literal.Integer $ fromIntegral $ (2 + 2 * slotCount) * wordBytes
            shadowStackOperand = Assembly.LocalOperand shadowStack
            shadowStackParameterOperand = Assembly.LocalOperand shadowStackParameter
        emit $ Assembly.StackAllocate shadowStack shadowStackSize
        store shadowStackOperand shadowStackParameterOperand
        shadowStackSizeSlot <- addPointer "shadow_stack_frame_size" shadowStackOperand $ Assembly.Lit $ Literal.Integer wordBytes
        store shadowStackSizeSlot $ Assembly.Lit $ Literal.Integer $ fromIntegral slotCount
        pure shadowStackParameter

-------------------------------------------------------------------------------

indexOperand :: Index v -> Environment v -> Operand
indexOperand index env = do
  let var =
        Context.lookupIndexVar index $ _context env
  fromMaybe (panic "ClosureConvertedToAssembly.indexOperand") $
    IntMap.lookup var $ _varLocations env

globalConstantOperand :: Name.Lifted -> Builder Operand
globalConstantOperand name = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  pure $ case signature of
    Representation.ConstantSignature representation ->
      Indirect $
        Assembly.GlobalConstant name $ case representation of
          Representation.Empty -> Assembly.WordPointer
          Representation.Direct _ -> Assembly.Word
          Representation.Indirect _ -> Assembly.WordPointer
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
  addPointer

heapAllocate :: Assembly.NameSuggestion -> Word8 -> Assembly.Operand -> Builder Assembly.Operand
heapAllocate nameSuggestion constructorTag size = do
  destination <- freshLocal $ nameSuggestion <> "_with_heap_pointer_and_limit"
  shadowStack <- Assembly.LocalOperand <$> gets _shadowStack
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  emit $ Assembly.HeapAllocate {destination, shadowStack, heapPointer, heapLimit, constructorTag, size}
  let destinationOperand = Assembly.LocalOperand destination
  result <- extractValue nameSuggestion destinationOperand 0
  heapPointer' <- extractValue "heap_pointer" destinationOperand 1
  heapLimit' <- extractValue "heap_limit" destinationOperand 2
  modify $ \s -> s {_heapPointer = heapPointer', _heapLimit = heapLimit'}
  pure result

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
    lift $ do
      value <- Evaluation.evaluate (Context.toEnvironment $ _context env) term
      typeValue <- TypeOf.typeOf (_context env) value
      typeRepresentation <- ClosureConverted.Representation.typeRepresentation (Context.toEnvironment $ _context env) typeValue
      type_ <- Readback.readback (Context.toEnvironment $ _context env) typeValue
      pure (type_, typeRepresentation)
  typeOperand <- generateType env type_
  pure (typeOperand, typeRepresentation)

sizeOfType :: Operand -> Builder Assembly.Operand
sizeOfType =
  forceDirect

switch ::
  Assembly.Return (Assembly.Type, Assembly.NameSuggestion) ->
  Assembly.Operand ->
  [(Integer, Builder (Assembly.Return Assembly.Operand))] ->
  Builder (Assembly.Return Assembly.Operand) ->
  Builder (Assembly.Return Assembly.Operand)
switch returnType scrutinee branches defaultBranch = do
  initialNextShadowStackSlot <- gets _nextShadowStackSlot
  initialHeapPointer <- gets _heapPointer
  initialHeapLimit <- gets _heapLimit
  let wrapBranch branch = subBuilder $ do
        modify $ \s ->
          s
            { _nextShadowStackSlot = initialNextShadowStackSlot
            , _heapPointer = initialHeapPointer
            , _heapLimit = initialHeapLimit
            }
        result <- branch
        nextShadowStackSlot <- gets _nextShadowStackSlot
        heapPointer <- gets _heapPointer
        heapLimit <- gets _heapLimit
        pure
          ( case result of
              Assembly.Void -> Assembly.Return $ Assembly.StructOperand [heapPointer, heapLimit]
              Assembly.Return result' -> Assembly.Return $ Assembly.StructOperand [result', heapPointer, heapLimit]
          , nextShadowStackSlot
          )

  ((defaultReturn, defaultNextShadowStackSlot), defaultInstructions) <- wrapBranch defaultBranch
  branches' <- forM branches $ \(i, branch) -> do
    ((branchReturn, branchNextShadowStackSlot), branchInstructions) <- wrapBranch branch
    pure ((i, Assembly.BasicBlock branchInstructions branchReturn), branchNextShadowStackSlot)
  let branchNextShadowStackSlots = snd <$> branches'
  when (any (/= defaultNextShadowStackSlot) branchNextShadowStackSlots) $
    panic "ClosureConvertedToAssembly.switch: Shadow stack mismatch"
  modify $ \s -> s {_nextShadowStackSlot = defaultNextShadowStackSlot}
  case returnType of
    Assembly.Void -> do
      resultLocal <- freshLocal "heap_pointer_and_limit"
      let resultType = Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer]
          resultOperand = Assembly.LocalOperand resultLocal
      emit $ Assembly.Switch (Assembly.Return (resultType, resultLocal)) scrutinee (fst <$> branches') $ Assembly.BasicBlock defaultInstructions defaultReturn
      heapPointer <- extractValue "heap_pointer" resultOperand 0
      heapLimit <- extractValue "heap_limit" resultOperand 1
      modify $ \s -> s {_heapPointer = heapPointer, _heapLimit = heapLimit}
      pure Assembly.Void
    Assembly.Return (type_, nameSuggestion) -> do
      resultLocal <- freshLocal $ nameSuggestion <> "_with_heap_pointer_and_limit"
      let resultType = Assembly.Struct [type_, Assembly.WordPointer, Assembly.WordPointer]
          resultOperand = Assembly.LocalOperand resultLocal
      emit $ Assembly.Switch (Assembly.Return (resultType, resultLocal)) scrutinee (fst <$> branches') $ Assembly.BasicBlock defaultInstructions defaultReturn
      result <- extractValue nameSuggestion resultOperand 0
      heapPointer <- extractValue "heap_pointer" resultOperand 1
      heapLimit <- extractValue "heap_limit" resultOperand 2
      modify $ \s -> s {_heapPointer = heapPointer, _heapLimit = heapLimit}
      pure $ Assembly.Return result

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

callVoid :: Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Builder ()
callVoid global args = do
  resultStruct <- freshLocal "call_result_struct"
  shadowStack <- gets _shadowStack
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  let returnType = Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer]
      args' =
        (Assembly.WordPointer, Assembly.LocalOperand shadowStack) :
        (Assembly.WordPointer, heapPointer) :
        (Assembly.WordPointer, heapLimit) :
        args
  emit $ Assembly.Call (Assembly.Return (returnType, resultStruct)) (Assembly.GlobalFunction global (Assembly.Return returnType) $ fst <$> args') args'
  let resultStructOperand = Assembly.LocalOperand resultStruct
  heapPointer' <- extractValue "heap_pointer" resultStructOperand 0
  heapLimit' <- extractValue "heap_limit" resultStructOperand 1
  modify $ \s ->
    s
      { _heapPointer = heapPointer'
      , _heapLimit = heapLimit'
      }
  pure ()

callDirect :: Assembly.NameSuggestion -> Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Builder Assembly.Operand
callDirect nameSuggestion global args = do
  resultStruct <- freshLocal $ nameSuggestion <> "_struct"
  shadowStack <- gets _shadowStack
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  let returnType = Assembly.Struct [Assembly.Word, Assembly.WordPointer, Assembly.WordPointer]
      args' =
        (Assembly.WordPointer, Assembly.LocalOperand shadowStack) :
        (Assembly.WordPointer, heapPointer) :
        (Assembly.WordPointer, heapLimit) :
        args
  emit $
    Assembly.Call
      (Assembly.Return (returnType, resultStruct))
      (Assembly.GlobalFunction global (Assembly.Return returnType) $ fst <$> args')
      args'
  let resultStructOperand = Assembly.LocalOperand resultStruct
  result <- extractValue nameSuggestion resultStructOperand 0
  heapPointer' <- extractValue "heap_pointer" resultStructOperand 1
  heapLimit' <- extractValue "heap_limit" resultStructOperand 2
  modify $ \s ->
    s
      { _heapPointer = heapPointer'
      , _heapLimit = heapLimit'
      }
  pure result

callIndirect :: Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Assembly.Operand -> Builder ()
callIndirect global args returnLocation =
  callVoid global ((Assembly.WordPointer, returnLocation) : args)

callInitFunction :: Assembly.NameSuggestion -> Name.Lifted -> [(Assembly.Type, Assembly.Operand)] -> Builder Assembly.Operand
callInitFunction nameSuggestion global args = do
  resultStruct <- freshLocal $ nameSuggestion <> "_struct"
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  let returnType = Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer, Assembly.WordPointer]
      args' =
        (Assembly.WordPointer, heapPointer) :
        (Assembly.WordPointer, heapLimit) :
        args
  emit $
    Assembly.Call
      (Assembly.Return (returnType, resultStruct))
      (Assembly.GlobalFunction global (Assembly.Return returnType) $ fst <$> args')
      args'
  let resultStructOperand = Assembly.LocalOperand resultStruct
  result <- extractValue nameSuggestion resultStructOperand 0
  heapPointer' <- extractValue "heap_pointer" resultStructOperand 1
  heapLimit' <- extractValue "heap_limit" resultStructOperand 2
  modify $ \s ->
    s
      { _heapPointer = heapPointer'
      , _heapLimit = heapLimit'
      }
  pure result

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

generateModuleInits :: [Name.Module] -> M Assembly.Definition
generateModuleInits moduleNames =
  runBuilder $ do
    Assembly.LocalOperand heapPointerParameter <- gets _heapPointer
    Assembly.LocalOperand heapLimitParameter <- gets _heapLimit
    globalPointer <- freshLocal "globals"
    let globalPointerOperand = Assembly.LocalOperand globalPointer
    foldM_ (go globalPointerOperand) globalPointerOperand moduleNames
    instructions <- gets _instructions
    pure $
      Assembly.FunctionDefinition
        Assembly.Void
        [(Assembly.WordPointer, heapPointerParameter), (Assembly.WordPointer, heapLimitParameter), (Assembly.WordPointer, globalPointer)]
        $ Assembly.BasicBlock (toList instructions) Assembly.Void
  where
    go globalBasePointer globalPointer moduleName =
      callInitFunction "globals" (moduleInitName moduleName) [(Assembly.WordPointer, globalBasePointer), (Assembly.WordPointer, globalPointer)]

generateModuleInit ::
  Name.Module ->
  [(Name.Lifted, Assembly.Definition)] ->
  M [(Name.Lifted, Assembly.Definition)]
generateModuleInit moduleName definitions =
  runBuilder $ do
    Assembly.LocalOperand heapPointerParameter <- gets _heapPointer
    Assembly.LocalOperand heapLimitParameter <- gets _heapLimit
    globalBasePointer <- freshLocal "globals_base"
    let globalBasePointerOperand = Assembly.LocalOperand globalBasePointer
    globalPointer <- freshLocal "globals"
    inited <- load "inited" $ Assembly.GlobalConstant initedName Assembly.Word
    Assembly.Return globalPointer' <-
      switch
        (Assembly.Return (Assembly.WordPointer, "globals"))
        inited
        [
          ( 0
          , do
              initGlobal initedName Assembly.Word $ Assembly.Lit $ Literal.Integer 1
              moduleHeader <- fetch $ Query.ModuleHeader moduleName
              globalPointer' <- foldM (initImport globalBasePointerOperand) (Assembly.LocalOperand globalPointer) $ Module._imports moduleHeader
              globalPointer'' <- foldM (initDefinition globalBasePointerOperand) globalPointer' definitions
              pure $ Assembly.Return globalPointer''
          )
        ]
        $ pure $ Assembly.Return $ Assembly.LocalOperand globalPointer
    heapPointer <- gets _heapPointer
    heapLimit <- gets _heapLimit
    instructions <- gets _instructions
    pure
      [
        ( moduleInitName moduleName
        , Assembly.FunctionDefinition
            ( Assembly.Return $ Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer, Assembly.WordPointer]
            )
            [ (Assembly.WordPointer, heapPointerParameter)
            , (Assembly.WordPointer, heapLimitParameter)
            , (Assembly.WordPointer, globalBasePointer)
            , (Assembly.WordPointer, globalPointer)
            ]
            ( Assembly.BasicBlock (toList instructions) $
                Assembly.Return $ Assembly.StructOperand [globalPointer', heapPointer, heapLimit]
            )
        )
      ,
        ( initedName
        , Assembly.KnownConstantDefinition Assembly.Word (Literal.Integer 0) False
        )
      ]
  where
    initedName = moduleInitedName moduleName
    initImport globalBasePointer globalPointer import_ =
      callInitFunction
        "globals"
        (moduleInitName $ Module._module import_)
        [(Assembly.WordPointer, globalBasePointer), (Assembly.WordPointer, globalPointer)]

    initDefinition globalBasePointer globalPointer (name, definition) =
      case definition of
        Assembly.KnownConstantDefinition {} ->
          pure globalPointer
        Assembly.ConstantDefinition {} ->
          callInitFunction "globals" (initDefinitionName name) [(Assembly.WordPointer, globalBasePointer), (Assembly.WordPointer, globalPointer)]
        Assembly.FunctionDefinition {} ->
          pure globalPointer

withFunctionDefinitionParameters ::
  Builder ((Assembly.Return Assembly.Type -> [(Assembly.Type, Assembly.Local)] -> Assembly.BasicBlock -> Assembly.Definition) -> a) ->
  Builder a
withFunctionDefinitionParameters m = do
  Assembly.LocalOperand heapPointerParameter <- gets _heapPointer
  Assembly.LocalOperand heapLimitParameter <- gets _heapLimit
  mkDefinition <- m
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  pure $
    mkDefinition $ \returnType parameters (Assembly.BasicBlock instructions returnOperand) ->
      Assembly.FunctionDefinition
        ( case returnType of
            Assembly.Void -> Assembly.Return $ Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer]
            Assembly.Return type_ -> Assembly.Return $ Assembly.Struct [type_, Assembly.WordPointer, Assembly.WordPointer]
        )
        ((Assembly.WordPointer, heapPointerParameter) : (Assembly.WordPointer, heapLimitParameter) : parameters)
        ( Assembly.BasicBlock instructions $
            case returnOperand of
              Assembly.Void -> Assembly.Return $ Assembly.StructOperand [heapPointer, heapLimit]
              Assembly.Return operand -> Assembly.Return $ Assembly.StructOperand [operand, heapPointer, heapLimit]
        )

generateDefinition :: Name.Lifted -> Syntax.Definition -> M (Maybe Assembly.Definition)
generateDefinition name@(Name.Lifted qualifiedName _) definition = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  let env =
        emptyEnvironment $ Scope.KeyedName Scope.Definition qualifiedName
  runBuilder $ do
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
        term <- Builder $ lift $ ClosureConverted.Representation.compileData (Context.toEnvironment $ _context env) qualifiedName constructors
        Just <$> generateGlobal env name representation term
      (Syntax.DataDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: DataDefinition without ConstantSignature"
      (Syntax.ParameterisedDataDefinition _ tele, Representation.FunctionSignature parameterRepresentations returnRepresentation) -> do
        tele' <- Builder $ lift $ ClosureConverted.Representation.compileParameterisedData (Context.toEnvironment $ _context env) qualifiedName tele
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
        Representation.Empty -> makeConstantDefinition Assembly.WordPointer $ \globalPointer -> do
          (_, deallocateTerm) <- generateTypedTerm env term (Direct emptyTypeOperand) representation
          sequence_ deallocateTerm
          pure globalPointer
        -- TODO use containsHeapPointers?
        Representation.Direct _containsHeapPointers -> makeConstantDefinition Assembly.Word $ \globalPointer -> do
          (result, deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) representation
          directResult <- forceDirect result
          sequence_ deallocateTerm
          initGlobal name Assembly.Word directResult
          pure globalPointer
        Representation.Indirect _containsHeapPointers ->
          makeConstantDefinition Assembly.WordPointer $ \globalPointer -> do
            (type_, _representation) <- typeOf env term
            typeSize <- sizeOfType type_
            globalPointer' <- globalAllocate "globals" globalPointer typeSize
            storeTerm env term globalPointer type_
            initGlobal name Assembly.WordPointer globalPointer
            pure globalPointer'

makeConstantDefinition ::
  Assembly.Type ->
  (Assembly.Operand -> Builder Assembly.Operand) ->
  Builder Assembly.Definition
makeConstantDefinition type_ m = do
  Assembly.LocalOperand heapPointerParameter <- gets _heapPointer
  Assembly.LocalOperand heapLimitParameter <- gets _heapLimit
  globalPointer <- freshLocal "globals"
  let globalPointerOperand = Assembly.LocalOperand globalPointer
  globalBasePointer <- freshLocal "globals_base"
  globalPointer' <- m globalPointerOperand
  instructions <- gets _instructions
  shadowStackInitInstructions <- shadowStackInitFromGlobals globalBasePointer globalPointer
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  pure $
    Assembly.ConstantDefinition
      type_
      ( Assembly.Return $
          Assembly.Struct
            [ Assembly.WordPointer
            , Assembly.WordPointer
            , Assembly.WordPointer
            ]
      )
      [ (Assembly.WordPointer, heapPointerParameter)
      , (Assembly.WordPointer, heapLimitParameter)
      , (Assembly.WordPointer, globalBasePointer)
      , (Assembly.WordPointer, globalPointer)
      ]
      ( Assembly.BasicBlock (shadowStackInitInstructions <> toList instructions) $
          Assembly.Return $
            Assembly.StructOperand
              [ globalPointer'
              , heapPointer
              , heapLimit
              ]
      )

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
  Tsil (Assembly.Type, Assembly.Local) ->
  Builder Assembly.Definition
generateFunction env returnRepresentation tele parameterRepresentations params =
  case (tele, parameterRepresentations) of
    (Telescope.Empty term, []) ->
      case returnRepresentation of
        Representation.Empty ->
          makeFunctionDefinition Assembly.Void (toList params) $ do
            (_, deallocateTerm) <- generateTypedTerm env term (Direct emptyTypeOperand) returnRepresentation
            sequence_ deallocateTerm
            pure Assembly.Void
        Representation.Direct _ ->
          makeFunctionDefinition (Assembly.Return Assembly.Word) (toList params) $ do
            (result, deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) returnRepresentation
            directResult <- forceDirect result
            sequence_ deallocateTerm
            pure $ Assembly.Return directResult
        Representation.Indirect _ -> do
          returnLocation <- freshLocal "return_location"
          makeFunctionDefinition Assembly.Void ((Assembly.WordPointer, returnLocation) : toList params) $ do
            (type_, _representation) <- typeOf env term
            storeTerm env term (Assembly.LocalOperand returnLocation) type_
            pure Assembly.Void
    (Telescope.Extend (Name name) type_ _plicity tele', parameterRepresentation : parameterRepresentations') -> do
      (params', paramOperand) <-
        case parameterRepresentation of
          Representation.Empty ->
            pure (params, Empty)
          Representation.Direct Representation.Doesn'tContainHeapPointers -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> (Assembly.Word, local), Direct $ Assembly.LocalOperand local)
          Representation.Direct Representation.MightContainHeapPointers -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> (Assembly.WordPointer, local), Indirect $ Assembly.LocalOperand local)
          Representation.Indirect _ -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure (params Tsil.:> (Assembly.WordPointer, local), Indirect $ Assembly.LocalOperand local)

      env' <- extend env type_ paramOperand
      generateFunction env' returnRepresentation tele' parameterRepresentations' params'
    _ ->
      panic "ClosureConvertedToAssembly.generateFunction: mismatched function telescope and signature"

makeFunctionDefinition ::
  Assembly.Return Assembly.Type ->
  [(Assembly.Type, Assembly.Local)] ->
  Builder (Assembly.Return Assembly.Operand) ->
  Builder Assembly.Definition
makeFunctionDefinition returnType parameters m = do
  Assembly.LocalOperand heapPointerParameter <- gets _heapPointer
  Assembly.LocalOperand heapLimitParameter <- gets _heapLimit
  returnOperand <- m
  heapPointer <- gets _heapPointer
  heapLimit <- gets _heapLimit
  instructions <- gets _instructions
  (shadowStackParameter, shadowStackInitInstructions) <- shadowStackInit
  pure $
    Assembly.FunctionDefinition
      ( case returnType of
          Assembly.Void -> Assembly.Return $ Assembly.Struct [Assembly.WordPointer, Assembly.WordPointer]
          Assembly.Return type_ -> Assembly.Return $ Assembly.Struct [type_, Assembly.WordPointer, Assembly.WordPointer]
      )
      ( (Assembly.WordPointer, shadowStackParameter) :
        (Assembly.WordPointer, heapPointerParameter) :
        (Assembly.WordPointer, heapLimitParameter) :
        parameters
      )
      ( Assembly.BasicBlock (shadowStackInitInstructions <> toList instructions) $
          case returnOperand of
            Assembly.Void -> Assembly.Return $ Assembly.StructOperand [heapPointer, heapLimit]
            Assembly.Return operand -> Assembly.Return $ Assembly.StructOperand [operand, heapPointer, heapLimit]
      )

-------------------------------------------------------------------------------

generateType :: Environment v -> Syntax.Type v -> Builder Operand
generateType env type_ = do
  (type', maybeDeallocateType) <- generateTypedTerm env type_ (Direct pointerBytesOperand) $ Representation.Direct Representation.Doesn'tContainHeapPointers
  case maybeDeallocateType of
    Nothing ->
      pure type'
    Just deallocateType -> do
      directType <- forceDirect type'
      deallocateType
      pure $ Direct directType

generateTypedTerm :: Environment v -> Syntax.Term v -> Operand -> Representation -> Builder (Operand, Maybe (Builder ()))
generateTypedTerm env term type_ representation = do
  let containsHeapPointers = Representation.containsHeapPointers representation
      stackAllocateIt = do
        typeSize <- sizeOfType type_
        stack <- saveStack
        termLocation <- stackAllocate "term_location" typeSize
        unregisterShadowStackSlot <- case containsHeapPointers of
          Representation.Doesn'tContainHeapPointers -> pure (pure ())
          Representation.MightContainHeapPointers -> registerShadowStackSlot typeSize termLocation
        storeTerm env term termLocation type_
        pure
          ( Indirect termLocation
          , Just $ do
              unregisterShadowStackSlot
              restoreStack stack
          )
  case (term, containsHeapPointers) of
    (Syntax.Var index, _) ->
      pure (indexOperand index env, Nothing)
    (Syntax.Global global, _) -> do
      operand <- globalConstantOperand global
      pure (operand, Nothing)
    (Syntax.Con {}, _) ->
      stackAllocateIt -- TODO
    (Syntax.Lit lit, _) ->
      pure (Direct $ Assembly.Lit lit, Nothing)
    (Syntax.Let _name term' termType body, _) -> do
      typeValue <- Builder $ lift $ Evaluation.evaluate (Context.toEnvironment $ _context env) termType
      typeRepresentation <- Builder $ lift $ ClosureConverted.Representation.typeRepresentation (Context.toEnvironment $ _context env) typeValue
      termType' <- generateType env termType
      (term'', deallocateTerm) <- generateTypedTerm env term' termType' typeRepresentation
      env' <- extend env termType term''
      (result, deallocateBody) <- generateTypedTerm env' body type_ representation
      pure (result, (>>) <$> deallocateBody <*> deallocateTerm)
    (Syntax.Function _, _) ->
      pure (Direct pointerBytesOperand, Nothing)
    (Syntax.Apply global arguments, Representation.Doesn'tContainHeapPointers) -> do
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
        Representation.Direct _containsHeapPointers -> do
          (arguments', deallocateArguments) <- generateArguments env $ zip arguments argumentRepresentations
          result <- callDirect "call_result" global arguments'
          deallocateArguments
          pure (Direct result, Nothing)
        Representation.Indirect _containsHeapPointers ->
          stackAllocateIt
    (Syntax.Pi {}, _) ->
      pure (Direct pointerBytesOperand, Nothing)
    (Syntax.Closure {}, _) ->
      stackAllocateIt
    (Syntax.ApplyClosure {}, _) ->
      stackAllocateIt
    (Syntax.Case {}, _) ->
      stackAllocateIt
    (_, Representation.MightContainHeapPointers) ->
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
                pure $ do
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
          typeValue <- Builder $ lift $ boxedConstructorSize (Context.toEnvironment $ _context env) con params args
          type_ <- Builder $ lift $ Readback.readback (Context.toEnvironment $ _context env) typeValue
          type' <- generateType env type_
          size <- sizeOfType type'
          heapLocation <-
            case maybeTag of
              Nothing -> do
                heapLocation <- heapAllocate "constructor_heap_object" 0 size
                store returnLocation heapLocation
                foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) args
                pure heapLocation
              Just tag
                | tag < 0xFF -> do
                  heapLocation <- heapAllocate "constructor_heap_object" (fromIntegral tag) size
                  store returnLocation heapLocation
                  foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) args
                  pure heapLocation
                | otherwise -> do
                  sizeWithTag <- add "size_with_tag" size $ Assembly.Lit $ Literal.Integer tagBytes
                  heapLocation <- heapAllocate "constructor_heap_object" 0xFF sizeWithTag
                  store returnLocation heapLocation
                  foldM_ go (pure $ Assembly.Lit $ Literal.Integer 0) tagArgs
                  pure heapLocation
          store returnLocation heapLocation
    Syntax.Lit lit ->
      store returnLocation (Assembly.Lit lit)
    Syntax.Let _name term' type_ body -> do
      typeValue <- Builder $ lift $ Evaluation.evaluate (Context.toEnvironment $ _context env) type_
      typeRepresentation <- Builder $ lift $ ClosureConverted.Representation.typeRepresentation (Context.toEnvironment $ _context env) typeValue
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
        Representation.Direct _containsHeapPointers -> do
          result <- callDirect "call_result" global arguments'
          store returnLocation result
        Representation.Indirect _containsHeapPointers -> do
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
              (Syntax.Apply (Name.Lifted Builtin.FailName 0) [Syntax.Global $ Name.Lifted Builtin.UnitName 0])
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
              [ ( fromIntegral branchTag
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
          taggedPointer <- load "tagged_heap_scrutinee_pointer" scrutinee''
          constructorTag <- extractHeapPointerConstructorTag "heap_scrutinee_tag" taggedPointer
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
              [ ( lit
                , do
                    storeTerm env branch returnLocation returnType
                    pure Assembly.Void
                )
              | (Literal.Integer lit, branch) <- OrderedHashMap.toList literalBranches
              ]
              ( do
                  storeTerm env defaultBranch returnLocation returnType
                  pure Assembly.Void
              )

storeUnboxedBranch ::
  Environment v ->
  (Assembly.NameSuggestion -> Builder Assembly.Operand) ->
  Telescope Name Syntax.Type Syntax.Term v ->
  Assembly.Operand ->
  Operand ->
  Builder ()
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

storeBoxedBranch ::
  Environment v ->
  Builder Assembly.Operand ->
  (Assembly.NameSuggestion -> Builder Assembly.Operand) ->
  Telescope Name Syntax.Type Syntax.Term v ->
  Assembly.Operand ->
  Operand ->
  Builder ()
storeBoxedBranch env constructorBasePointerBuilder constructorFieldOffsetBuilder tele returnLocation returnType =
  case tele of
    Telescope.Extend (Name name) type_ _plicity tele' -> do
      constructorFieldOffset <- constructorFieldOffsetBuilder $ Assembly.NameSuggestion $ name <> "_offset"
      type' <- generateType env type_
      typeSize <- sizeOfType type'
      stack <- saveStack
      stackConstructorField <- stackAllocate (Assembly.NameSuggestion $ name <> "_stack") pointerBytesOperand
      typeRepresentation <- Builder $
        lift $ do
          typeValue <- Evaluation.evaluate (Context.toEnvironment $ _context env) type_
          ClosureConverted.Representation.typeRepresentation (Context.toEnvironment $ _context env) typeValue
      unregisterShadowStackSlot <- case Representation.containsHeapPointers typeRepresentation of
        Representation.Doesn'tContainHeapPointers -> pure (pure ())
        Representation.MightContainHeapPointers -> registerShadowStackSlot typeSize stackConstructorField
      constructorBasePointer <- constructorBasePointerBuilder
      constructorField <- addPointer (Assembly.NameSuggestion name) constructorBasePointer constructorFieldOffset
      copy stackConstructorField (Indirect constructorField) typeSize
      let nextConstructorFieldOffsetBuilder nameSuggestion =
            add nameSuggestion constructorFieldOffset typeSize
      env' <- extend env type_ $ Indirect stackConstructorField
      storeBoxedBranch env' constructorBasePointerBuilder nextConstructorFieldOffsetBuilder tele' returnLocation returnType
      unregisterShadowStackSlot
      restoreStack stack
    Telescope.Empty branch ->
      storeTerm env branch returnLocation returnType

generateArguments :: Environment v -> [(Syntax.Term v, Representation)] -> Builder ([(Assembly.Type, Assembly.Operand)], Builder ())
generateArguments env arguments = do
  (argumentGenerators, outerDeallocators) <- unzip <$> mapM (uncurry $ generateArgument env) arguments
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
    Representation.Direct Representation.Doesn'tContainHeapPointers -> do
      (term', deallocateTerm) <- generateTypedTerm env term (Direct directTypeOperand) representation
      pure
        ( do
            directTerm <- forceDirect term'
            pure ([(Assembly.Word, directTerm)], pure ())
        , sequence_ deallocateTerm
        )
    Representation.Direct Representation.MightContainHeapPointers -> indirectCase
    Representation.Indirect _containsHeapPointers -> indirectCase
  where
    indirectCase = do
      (type_, representation_) <- typeOf env term
      (termOperand, deallocateTermOperand) <- generateTypedTerm env term type_ representation_
      pure
        ( do
            (termLocation, deallocateTerm) <- forceIndirect termOperand
            pure ([(Assembly.WordPointer, termLocation)], deallocateTerm)
        , sequence_ deallocateTermOperand
        )

-------------------------------------------------------------------------------

boxedConstructorSize ::
  Domain.Environment v ->
  Name.QualifiedConstructor ->
  [Syntax.Term v] ->
  [Syntax.Term v] ->
  M Domain.Value
boxedConstructorSize env con params args = do
  tele <- fetch $ Query.ClosureConvertedConstructorType con
  params' <- mapM (Evaluation.evaluate env) params
  args' <- mapM (Evaluation.evaluate env) args
  maybeResult <- Evaluation.applyTelescope env (Telescope.fromVoid tele) params' $ \env' type_ -> do
    type' <- Evaluation.evaluate env' type_
    size <- ClosureConverted.Representation.compileBoxedConstructorFields env' type' args'
    Evaluation.evaluate env' size
  case maybeResult of
    Nothing -> panic "boxedConstructorSize: Data params length mismatch"
    Just result -> pure result
