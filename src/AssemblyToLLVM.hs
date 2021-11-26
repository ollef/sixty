{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module AssemblyToLLVM where

import qualified Assembly
import qualified ClosureConvertedToAssembly
import Data.Bitraversable
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as ShortByteString
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import Data.String (fromString)
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified LLVM.AST as LLVM
import qualified LLVM.AST.CallingConvention as LLVM.CallingConvention
import qualified LLVM.AST.Constant as LLVM.Constant
import qualified LLVM.AST.Global as LLVM.Global
import qualified LLVM.AST.Linkage as LLVM
import qualified LLVM.AST.ParameterAttribute as LLVM
import qualified LLVM.AST.ParameterAttribute as ParameterAttribute
import qualified LLVM.AST.Type as LLVM.Type
import qualified Literal
import qualified Name
import Prettyprinter
import Protolude hiding (IntMap, cast, local, moduleName)

type Assembler = State AssemblerState

data AssemblerState = AssemblerState
  { _locals :: HashMap Assembly.Local (Assembly.Type, LLVM.Operand)
  , _usedGlobals :: HashMap LLVM.Name LLVM.Global
  , _usedNames :: HashMap ShortByteString Int
  , _instructions :: Tsil (LLVM.Named LLVM.Instruction)
  , _basicBlockName :: LLVM.Name
  , _basicBlocks :: Tsil LLVM.BasicBlock
  }

llvmType :: Assembly.Type -> LLVM.Type
llvmType type_ =
  case type_ of
    Assembly.Word -> wordSizedInt
    Assembly.WordPointer -> wordPointer
    Assembly.FunctionPointer returnType argumentTypes ->
      LLVM.Type.ptr
        LLVM.FunctionType
          { resultType = llvmReturnType returnType
          , argumentTypes = llvmType <$> argumentTypes
          , isVarArg = False
          }
    Assembly.Struct types ->
      LLVM.Type.StructureType
        { isPacked = False
        , elementTypes = llvmType <$> types
        }

llvmParameterAttributes :: Assembly.Type -> [LLVM.ParameterAttribute]
llvmParameterAttributes type_ =
  case type_ of
    Assembly.Word -> []
    Assembly.WordPointer -> [LLVM.NonNull]
    Assembly.FunctionPointer {} -> [LLVM.NonNull]
    Assembly.Struct _ -> []

llvmReturnType :: Assembly.Return Assembly.Type -> LLVM.Type
llvmReturnType result =
  case result of
    Assembly.Void -> LLVM.Type.void
    Assembly.Return type_ -> llvmType type_

alignment :: Num a => a
alignment =
  8

wordBytes :: Num a => a
wordBytes =
  8

wordBits :: Num a => a
wordBits =
  64

wordSizedInt :: LLVM.Type
wordSizedInt =
  LLVM.Type.IntegerType wordBits

wordPointer :: LLVM.Type
wordPointer =
  LLVM.Type.ptr wordSizedInt

bytePointer :: LLVM.Type
bytePointer =
  LLVM.Type.ptr LLVM.Type.i8

emitInstruction :: LLVM.Named LLVM.Instruction -> Assembler ()
emitInstruction instruction =
  modify $ \s -> s {_instructions = _instructions s Tsil.:> instruction}

startBlock :: LLVM.Name -> Assembler ()
startBlock basicBlockName =
  modify $ \s -> s {_basicBlockName = basicBlockName}

endBlock :: LLVM.Named LLVM.Terminator -> Assembler ()
endBlock terminator =
  modify $ \s ->
    s
      { _instructions = mempty
      , _basicBlockName = panic "AssemblyToLLVM: not in a basic block"
      , _basicBlocks =
          _basicBlocks s
            Tsil.:> LLVM.BasicBlock (_basicBlockName s) (toList $ _instructions s) terminator
      }

freshName :: Assembly.NameSuggestion -> Assembler LLVM.Name
freshName (Assembly.NameSuggestion nameSuggestion) = do
  usedNames <- gets _usedNames
  let bsName =
        ShortByteString.toShort $ toUtf8 nameSuggestion

      i =
        HashMap.lookupDefault 0 bsName usedNames
  modify $ \s ->
    s
      { _usedNames = HashMap.insert bsName (i + 1) usedNames
      }
  pure $ LLVM.Name $ if i == 0 then bsName else bsName <> "$" <> ShortByteString.toShort (toUtf8 (show i :: Text))

activateLocal :: Assembly.Type -> Assembly.Local -> Assembler LLVM.Name
activateLocal type_ local@(Assembly.Local _ nameSuggestion) = do
  name <- freshName nameSuggestion
  modify $ \s ->
    s
      { _locals = HashMap.insert local (type_, LLVM.LocalReference (llvmType type_) name) $ _locals s
      }
  pure name

use :: LLVM.Global -> Assembler ()
use global =
  modify $ \s ->
    s
      { _usedGlobals = HashMap.insert (LLVM.Global.name global) global $ _usedGlobals s
      }

-------------------------------------------------------------------------------
memset0 :: LLVM.Operand -> LLVM.Operand -> Assembler ()
memset0 destination size = do
  let memsetResultType =
        LLVM.Type.void

      memsetArgumentTypes =
        [ bytePointer
        , LLVM.Type.i8
        , wordSizedInt
        , LLVM.Type.i1
        ]

      memsetType =
        LLVM.FunctionType
          { LLVM.resultType = memsetResultType
          , LLVM.argumentTypes = memsetArgumentTypes
          , LLVM.isVarArg = False
          }

      memsetName =
        LLVM.Name $ "llvm.memset.p0i8.i" <> fromString (show (wordBits :: Int))

      arguments =
        [ (destination, [ParameterAttribute.Alignment alignment])
        , (LLVM.ConstantOperand $ LLVM.Constant.Int {integerBits = 8, integerValue = 0}, [])
        , (size, [])
        , (LLVM.ConstantOperand $ LLVM.Constant.Int {integerBits = 1, integerValue = 0}, []) -- isvolatile
        ]

  use
    LLVM.functionDefaults
      { LLVM.Global.returnType = memsetResultType
      , LLVM.Global.name = memsetName
      , LLVM.Global.parameters =
          ( [LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] memsetArgumentTypes]
          , False
          )
      }
  emitInstruction $
    LLVM.Do
      LLVM.Call
        { tailCallKind = Nothing
        , callingConvention = LLVM.CallingConvention.C
        , returnAttributes = []
        , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference memsetType memsetName
        , arguments = arguments
        , functionAttributes = []
        , metadata = []
        }

-------------------------------------------------------------------------------

assembleModule :: Name.Module -> [(Name.Lifted, Assembly.Definition)] -> LLVM.Module
assembleModule (Name.Module moduleNameText) definitions = do
  let (assembledDefinitions, usedGlobals) =
        unzip $ foreach definitions $ uncurry assembleDefinition

      assembledDefinitions' =
        concat assembledDefinitions

      forwardDeclarations =
        HashMap.difference (mconcat usedGlobals) (HashSet.toMap $ HashSet.fromList (LLVM.Global.name <$> assembledDefinitions'))

  LLVM.Module
    { moduleName = ShortByteString.toShort $ toUtf8 moduleNameText
    , moduleSourceFileName = ""
    , moduleDataLayout = Nothing
    , moduleTargetTriple = Nothing
    , moduleDefinitions = LLVM.GlobalDefinition <$> HashMap.elems forwardDeclarations <> assembledDefinitions'
    }

assembleDefinition :: Name.Lifted -> Assembly.Definition -> ([LLVM.Global], HashMap LLVM.Name LLVM.Global)
assembleDefinition name@(Name.Lifted _ liftedNameNumber) definition =
  second _usedGlobals $
    flip
      runState
      AssemblerState
        { _locals = mempty
        , _usedNames = mempty
        , _usedGlobals = mempty
        , _instructions = mempty
        , _basicBlocks = mempty
        , _basicBlockName = panic "AssemblyToLLVM: not in a basic block"
        }
      $ case definition of
        Assembly.KnownConstantDefinition type_ (Literal.Integer value) isConstant -> do
          let type' = llvmType type_
          pure
            [ LLVM.globalVariableDefaults
                { LLVM.Global.name = assembleName name
                , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
                , LLVM.Global.type' = type'
                , LLVM.Global.initializer =
                    Just
                      LLVM.Constant.Int
                        { integerBits = wordBits
                        , integerValue = value
                        }
                , LLVM.Global.linkage = linkage
                , LLVM.Global.isConstant = isConstant
                }
            ]
        Assembly.ConstantDefinition type_ functionReturnType parameters basicBlock -> do
          parameters' <- mapM (uncurry activateLocal) parameters
          assembleBasicBlockReturningResult functionReturnType basicBlock
          basicBlocks <- gets _basicBlocks
          let type' = llvmType type_
          pure
            [ LLVM.globalVariableDefaults
                { LLVM.Global.name = assembleName name
                , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
                , LLVM.Global.type' = type'
                , LLVM.Global.initializer = Just LLVM.Constant.Undef {constantType = type'}
                , LLVM.Global.linkage = linkage
                }
            , LLVM.Global.functionDefaults
                { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
                , LLVM.Global.returnType = llvmReturnType functionReturnType
                , LLVM.Global.name = assembleName $ ClosureConvertedToAssembly.initDefinitionName name
                , LLVM.Global.parameters = ([LLVM.Parameter wordPointer parameter [] | parameter <- parameters'], False)
                , LLVM.Global.alignment = alignment
                , LLVM.Global.basicBlocks = toList basicBlocks
                , LLVM.Global.linkage = LLVM.Private
                }
            ]
        Assembly.FunctionDefinition returnType parameters basicBlock -> do
          parameters' <- mapM (uncurry activateLocal) parameters
          assembleBasicBlockReturningResult returnType basicBlock
          basicBlocks <- gets _basicBlocks
          pure
            [ LLVM.Global.functionDefaults
                { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
                , LLVM.Global.returnType = llvmReturnType returnType
                , LLVM.Global.name = assembleName name
                , LLVM.Global.parameters = ([LLVM.Parameter (llvmType type_) parameter (llvmParameterAttributes type_) | ((type_, _), parameter) <- zip parameters parameters'], False)
                , LLVM.Global.alignment = alignment
                , LLVM.Global.basicBlocks = toList basicBlocks
                , LLVM.Global.linkage = linkage
                }
            ]
  where
    linkage =
      case liftedNameNumber of
        0 ->
          LLVM.External
        _ ->
          LLVM.Private

assembleName :: Name.Lifted -> LLVM.Name
assembleName =
  LLVM.Name . ShortByteString.toShort . toUtf8 . Assembly.nameText

assembleBasicBlockReturningResult :: Assembly.Return Assembly.Type -> Assembly.BasicBlock -> Assembler ()
assembleBasicBlockReturningResult returnType (Assembly.BasicBlock instructions result) = do
  blockName <- freshName "entry"
  startBlock blockName
  mapM_ assembleInstruction instructions
  returnResult returnType result

returnResult :: Assembly.Return Assembly.Type -> Assembly.Return Assembly.Operand -> Assembler ()
returnResult returnType_ result = do
  case (returnType_, result) of
    (Assembly.Void, Assembly.Void) -> do
      endBlock $ LLVM.Do LLVM.Ret {returnOperand = Nothing, metadata' = mempty}
    (Assembly.Return type_, Assembly.Return res) -> do
      operand <- assembleOperandAndCastTo type_ res
      endBlock $ LLVM.Do LLVM.Ret {returnOperand = Just operand, metadata' = mempty}
    _ ->
      panic "AssemblyToLLVM.returnResult: return type mismatch"

assembleInstruction :: Assembly.Instruction -> Assembler ()
assembleInstruction instruction =
  case instruction of
    Assembly.Copy destination source size -> do
      destination' <- assembleOperandAndCastTo Assembly.WordPointer destination
      source' <- assembleOperandAndCastTo Assembly.WordPointer source
      size' <- assembleOperandAndCastTo Assembly.Word size
      destination'' <- freshName "destination"
      source'' <- freshName "source"
      let memcpyName = LLVM.Name $ "llvm.memcpy.p0i8.p0i8.i" <> fromString (show (wordBits :: Int))
          memcpyResultType = LLVM.Type.void
          memcpyArgumentTypes =
            [ bytePointer
            , bytePointer
            , wordSizedInt
            , LLVM.Type.i32
            , LLVM.Type.i1
            ]
          memcpyType =
            LLVM.FunctionType
              { LLVM.resultType = memcpyResultType
              , LLVM.argumentTypes = memcpyArgumentTypes
              , LLVM.isVarArg = False
              }
          arguments =
            [ LLVM.LocalReference bytePointer destination''
            , LLVM.LocalReference bytePointer source''
            , size'
            , LLVM.ConstantOperand $ LLVM.Constant.Int 32 alignment
            , LLVM.ConstantOperand $ LLVM.Constant.Int 1 0 -- isvolatile
            ]
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = memcpyResultType
          , LLVM.Global.name = memcpyName
          , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] memcpyArgumentTypes], False)
          }
      emitInstruction $
        destination''
          LLVM.:= LLVM.BitCast
            { operand0 = destination'
            , type' = bytePointer
            , metadata = mempty
            }
      emitInstruction $
        source''
          LLVM.:= LLVM.BitCast
            { operand0 = source'
            , type' = bytePointer
            , metadata = mempty
            }
      emitInstruction $
        LLVM.Do
          LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference memcpyType memcpyName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
    Assembly.Call (Assembly.Return (returnType, destination)) function arguments -> do
      function' <- assembleOperandAndCastTo (Assembly.FunctionPointer (Assembly.Return returnType) $ fst <$> arguments) function
      arguments' <- mapM (uncurry assembleOperandAndCastTo) arguments
      destination' <- activateLocal returnType destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.Fast
            , returnAttributes = []
            , function = Right function'
            , arguments = [(arg, []) | arg <- arguments']
            , functionAttributes = []
            , metadata = []
            }
    Assembly.Call Assembly.Void function arguments -> do
      function' <- assembleOperandAndCastTo (Assembly.FunctionPointer Assembly.Void $ fst <$> arguments) function
      arguments' <- mapM (uncurry assembleOperandAndCastTo) arguments
      emitInstruction $
        LLVM.Do
          LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.Fast
            , returnAttributes = []
            , function = Right function'
            , arguments = [(arg, []) | arg <- arguments']
            , functionAttributes = []
            , metadata = []
            }
    Assembly.Load destination address -> do
      address' <- assembleOperandAndCastTo Assembly.WordPointer address
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Load
            { volatile = False
            , address = address'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
    Assembly.Store address value -> do
      address' <- assembleOperandAndCastTo Assembly.WordPointer address
      value' <- assembleOperandAndCastTo Assembly.Word value
      emitInstruction $
        LLVM.Do
          LLVM.Store
            { volatile = False
            , address = address'
            , value = value'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
    Assembly.InitGlobal global type_ value -> do
      value' <- assembleOperandAndCastTo type_ value
      emitInstruction $
        LLVM.Do
          LLVM.Store
            { volatile = False
            , address =
                LLVM.ConstantOperand $
                  LLVM.Constant.GlobalReference
                    (LLVM.Type.ptr $ llvmType type_)
                    (assembleName global)
            , value = value'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
    Assembly.Add destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Add
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
    Assembly.Sub destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Sub
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
    Assembly.Mul destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Mul
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
    Assembly.AddPointer destination pointerOperand wordOperand -> do
      pointerOperand' <- assembleOperandAndCastTo Assembly.WordPointer pointerOperand
      wordOperand' <- assembleOperandAndCastTo Assembly.Word wordOperand
      bytePointerName <- freshName "byte_pointer"
      emitInstruction $
        bytePointerName
          LLVM.:= LLVM.BitCast
            { operand0 = pointerOperand'
            , type' = bytePointer
            , metadata = mempty
            }
      resultBytePointer <- freshName "add_pointer_result"
      emitInstruction $
        resultBytePointer
          LLVM.:= LLVM.GetElementPtr
            { inBounds = False -- TODO can this be true even when there are empty types?
            , address = LLVM.LocalReference bytePointer bytePointerName
            , indices = [wordOperand']
            , metadata = mempty
            }
      destination' <- activateLocal Assembly.WordPointer destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.BitCast
            { operand0 = LLVM.LocalReference bytePointer resultBytePointer
            , type' = wordPointer
            , metadata = mempty
            }
    Assembly.StackAllocate destination size -> do
      destination' <- activateLocal Assembly.WordPointer destination
      destination'' <- freshName "destination"
      size' <- assembleOperandAndCastTo Assembly.Word size
      emitInstruction $
        destination''
          LLVM.:= LLVM.Alloca
            { numElements = Just size'
            , allocatedType = LLVM.Type.i8
            , alignment = alignment
            , metadata = mempty
            }
      memset0 (LLVM.LocalReference bytePointer destination'') size'
      emitInstruction $
        destination'
          LLVM.:= LLVM.BitCast
            { operand0 = LLVM.LocalReference bytePointer destination''
            , type' = wordPointer
            , metadata = mempty
            }
    Assembly.SaveStack destination -> do
      destination' <- activateLocal Assembly.WordPointer destination
      destination'' <- freshName "stack_byte_pointer"
      let stackSaveName = LLVM.Name "llvm.stacksave"
          stackSaveResultType = bytePointer
          stackSaveType =
            LLVM.FunctionType
              { LLVM.resultType = stackSaveResultType
              , LLVM.argumentTypes = []
              , LLVM.isVarArg = False
              }
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = stackSaveResultType
          , LLVM.Global.name = stackSaveName
          , LLVM.Global.parameters = ([], False)
          }
      emitInstruction $
        destination''
          LLVM.:= LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference stackSaveType stackSaveName
            , arguments = []
            , functionAttributes = []
            , metadata = []
            }
      emitInstruction $
        destination'
          LLVM.:= LLVM.BitCast
            { operand0 = LLVM.LocalReference bytePointer destination''
            , type' = wordPointer
            , metadata = mempty
            }
    Assembly.RestoreStack operand -> do
      operand' <- assembleOperandAndCastTo Assembly.WordPointer operand
      operand'' <- freshName "stack_byte_pointer"
      let stackRestoreName = LLVM.Name "llvm.stackrestore"
          stackRestoreResultType = LLVM.Type.void
          stackRestoreArgumentTypes = [bytePointer]
          stackSaveType =
            LLVM.FunctionType
              { LLVM.resultType = stackRestoreResultType
              , LLVM.argumentTypes = stackRestoreArgumentTypes
              , LLVM.isVarArg = False
              }
          arguments =
            [ LLVM.LocalReference bytePointer operand''
            ]
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = stackRestoreResultType
          , LLVM.Global.name = stackRestoreName
          , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] stackRestoreArgumentTypes], False)
          }
      emitInstruction $
        operand''
          LLVM.:= LLVM.BitCast
            { operand0 = operand'
            , type' = bytePointer
            , metadata = mempty
            }
      emitInstruction $
        LLVM.Do
          LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference stackSaveType stackRestoreName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
    Assembly.HeapAllocate {destination, shadowStack, heapPointer, heapLimit, constructorTag, size} -> do
      destination' <- activateLocal (Assembly.Struct [Assembly.Word, Assembly.WordPointer, Assembly.WordPointer]) destination
      shadowStack' <- assembleOperandAndCastTo Assembly.WordPointer shadowStack
      heapPointer' <- assembleOperandAndCastTo Assembly.WordPointer heapPointer
      heapLimit' <- assembleOperandAndCastTo Assembly.WordPointer heapLimit
      size' <- assembleOperandAndCastTo Assembly.Word size
      let heapAllocName = LLVM.Name "__regcall3__heap_alloc"
          heapAllocResultType = LLVM.Type.StructureType {isPacked = False, elementTypes = [wordSizedInt, wordPointer, wordPointer]}
          heapAllocArgumentTypes = [wordPointer, wordPointer, wordPointer, LLVM.Type.i8, wordSizedInt]
          heapAllocType =
            LLVM.FunctionType
              { LLVM.resultType = heapAllocResultType
              , LLVM.argumentTypes = heapAllocArgumentTypes
              , LLVM.isVarArg = False
              }
          arguments =
            [ shadowStack'
            , heapPointer'
            , heapLimit'
            , LLVM.ConstantOperand LLVM.Constant.Int {integerBits = 8, integerValue = fromIntegral constructorTag}
            , size'
            ]
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = heapAllocResultType
          , LLVM.Global.name = heapAllocName
          , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] heapAllocArgumentTypes], False)
          }
      emitInstruction $
        destination'
          LLVM.:= LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.X86_RegCall
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference heapAllocType heapAllocName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
    Assembly.ExtractHeapPointer destination pointer -> do
      destination' <- activateLocal Assembly.WordPointer destination
      pointer' <- assembleOperandAndCastTo Assembly.Word pointer
      let extractHeapPointerName = LLVM.Name "heap_object_pointer"
          extractHeapPointerResultType = wordPointer
          extractHeapPointerArgumentTypes = [wordSizedInt]
          extractHeapPointerType =
            LLVM.FunctionType
              { LLVM.resultType = extractHeapPointerResultType
              , LLVM.argumentTypes = extractHeapPointerArgumentTypes
              , LLVM.isVarArg = False
              }
          arguments = [pointer']
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = extractHeapPointerResultType
          , LLVM.Global.name = extractHeapPointerName
          , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] extractHeapPointerArgumentTypes], False)
          }
      emitInstruction $
        destination'
          LLVM.:= LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference extractHeapPointerType extractHeapPointerName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
    Assembly.ExtractHeapPointerConstructorTag destination pointer -> do
      destination' <- activateLocal Assembly.Word destination
      pointer' <- assembleOperandAndCastTo Assembly.Word pointer
      let extractConstructorTagName = LLVM.Name "heap_object_constructor_tag"
          extractConstructorTagResultType = wordSizedInt
          extractConstructorTagArgumentTypes = [wordSizedInt]
          extractHeapPointerType =
            LLVM.FunctionType
              { LLVM.resultType = extractConstructorTagResultType
              , LLVM.argumentTypes = extractConstructorTagArgumentTypes
              , LLVM.isVarArg = False
              }
          arguments = [pointer']
      use
        LLVM.functionDefaults
          { LLVM.Global.returnType = extractConstructorTagResultType
          , LLVM.Global.name = extractConstructorTagName
          , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0 ..] extractConstructorTagArgumentTypes], False)
          }
      emitInstruction $
        destination'
          LLVM.:= LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference extractHeapPointerType extractConstructorTagName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
    Assembly.ExtractValue destination struct index -> do
      (_nameSuggestion, structType, struct') <- assembleOperand struct
      case structType of
        Assembly.Struct types -> do
          let fieldType = types List.!! index
          destination' <- activateLocal fieldType destination
          emitInstruction $
            destination'
              LLVM.:= LLVM.ExtractValue
                { aggregate = struct'
                , indices' = [fromIntegral index]
                , metadata = mempty
                }
        _ -> panic "AssemblyToLLVM.assembleInstruction: ExtractValue of non-struct"
    Assembly.Switch destination scrutinee branches (Assembly.BasicBlock defaultBranchInstructions defaultBranchResult) -> do
      scrutinee' <- assembleOperandAndCastTo Assembly.Word scrutinee
      branchLabels <- forM branches $ \(i, _) -> do
        branchLabel <- freshName $ Assembly.NameSuggestion $ "branch_" <> show i
        pure
          ( LLVM.Constant.Int
              { integerBits = wordBits
              , integerValue = i
              }
          , branchLabel
          )
      defaultBranchLabel <- freshName "default"
      afterSwitchLabel <- freshName "after_switch"
      endBlock $
        LLVM.Do
          LLVM.Switch
            { operand0' = scrutinee'
            , dests = branchLabels
            , defaultDest = defaultBranchLabel
            , metadata' = mempty
            }
      branchResultOperands <- forM (zip branchLabels branches) $ \((_, branchLabel), (_, Assembly.BasicBlock instructions result)) -> do
        startBlock branchLabel
        mapM_ assembleInstruction instructions
        resultOperand <- forM ((,) . fst <$> destination <*> result) $ uncurry assembleOperandAndCastTo
        branchLabel' <- gets _basicBlockName
        endBlock $ LLVM.Do LLVM.Br {dest = afterSwitchLabel, metadata' = mempty}
        pure (resultOperand, branchLabel')
      startBlock defaultBranchLabel
      mapM_ assembleInstruction defaultBranchInstructions
      defaultResultOperand <- forM ((,) . fst <$> destination <*> defaultBranchResult) $ uncurry assembleOperandAndCastTo
      defaultBranchLabel' <- gets _basicBlockName
      endBlock $ LLVM.Do LLVM.Br {dest = afterSwitchLabel, metadata' = mempty}
      startBlock afterSwitchLabel
      case destination of
        Assembly.Void ->
          pure ()
        Assembly.Return (destinationType, destinationLocal) -> do
          destination' <- activateLocal destinationType destinationLocal
          let voidedIncomingValues = (defaultResultOperand, defaultBranchLabel') : branchResultOperands
              incomingValues =
                case traverse (bitraverse identity pure) voidedIncomingValues of
                  Assembly.Return incomingValues_ -> incomingValues_
                  Assembly.Void -> panic "AssemblyToLLVM: Switch with mismatch between instruction result and branch results"
          emitInstruction $
            destination'
              LLVM.:= LLVM.Phi
                { type' = llvmType destinationType
                , incomingValues = incomingValues
                , metadata = mempty
                }

assembleOperand :: Assembly.Operand -> Assembler (Assembly.NameSuggestion, Assembly.Type, LLVM.Operand)
assembleOperand operand = do
  case operand of
    Assembly.LocalOperand local@(Assembly.Local _ nameSuggestion) -> do
      locals <- gets _locals
      let (type_, operand') = HashMap.lookupDefault (panic $ "assembleOperandWithOperandType: no such local " <> show local) local locals
      pure (nameSuggestion, type_, operand')
    Assembly.GlobalConstant global globalType -> do
      let globalName = assembleName global
          globalNameText = Assembly.nameText global
          nameSuggestion = Assembly.NameSuggestion globalNameText
          llvmGlobalType = llvmType globalType
      use
        LLVM.globalVariableDefaults
          { LLVM.Global.name = globalName
          , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
          , LLVM.Global.isConstant = True
          , LLVM.Global.type' = llvmGlobalType
          }
      case globalType of
        Assembly.Word ->
          pure (nameSuggestion, Assembly.WordPointer, LLVM.ConstantOperand $ LLVM.Constant.GlobalReference wordPointer globalName)
        Assembly.WordPointer -> do
          destination <- freshName nameSuggestion
          emitInstruction $
            destination
              LLVM.:= LLVM.Load
                { volatile = False
                , address = LLVM.ConstantOperand $ LLVM.Constant.GlobalReference (LLVM.Type.ptr wordPointer) globalName
                , maybeAtomicity = Nothing
                , alignment = alignment
                , metadata = []
                }
          pure (nameSuggestion, Assembly.WordPointer, LLVM.LocalReference wordPointer destination)
        Assembly.FunctionPointer _ _ -> do
          let llvmType_ = llvmType globalType
          destination <- freshName nameSuggestion
          emitInstruction $
            destination
              LLVM.:= LLVM.Load
                { volatile = False
                , address = LLVM.ConstantOperand $ LLVM.Constant.GlobalReference llvmType_ globalName
                , maybeAtomicity = Nothing
                , alignment = alignment
                , metadata = []
                }
          pure (nameSuggestion, Assembly.WordPointer, LLVM.LocalReference llvmType_ destination)
        Assembly.Struct types ->
          pure (nameSuggestion, Assembly.Struct types, LLVM.ConstantOperand $ LLVM.Constant.GlobalReference wordPointer globalName)
    Assembly.GlobalFunction global returnType parameterTypes -> do
      let defType = Assembly.FunctionPointer returnType parameterTypes
          globalNameText = Assembly.nameText global
          nameSuggestion = Assembly.NameSuggestion globalNameText
          globalName = assembleName global
          globalType = llvmType defType
      use
        LLVM.functionDefaults
          { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
          , LLVM.Global.returnType = llvmReturnType returnType
          , LLVM.Global.name = globalName
          , LLVM.Global.parameters = ([LLVM.Parameter (llvmType parameterType) (LLVM.UnName parameter) [] | (parameter, parameterType) <- zip [0 ..] parameterTypes], False)
          , LLVM.Global.alignment = alignment
          }
      pure (nameSuggestion, defType, LLVM.ConstantOperand $ LLVM.Constant.GlobalReference globalType globalName)
    Assembly.StructOperand operands -> do
      typedOperands <- mapM assembleOperand operands
      let types = (\(_, type', _) -> type') <$> typedOperands
          operands' = (\(_, _, operand') -> operand') <$> typedOperands
          type_ = Assembly.Struct types
          llvmType_ = llvmType type_
          go (index, struct) fieldOperand = do
            struct' <- freshName "struct"
            emitInstruction $
              struct'
                LLVM.:= LLVM.InsertValue
                  { aggregate = struct
                  , element = fieldOperand
                  , indices' = [index]
                  , metadata = mempty
                  }
            pure (index + 1, LLVM.LocalReference llvmType_ struct')

      result <- snd <$> foldM go (0, LLVM.ConstantOperand $ LLVM.Constant.Undef {constantType = llvmType_}) operands'
      pure ("struct", type_, result)
    Assembly.Lit lit ->
      case lit of
        Literal.Integer int ->
          pure
            ( "literal"
            , Assembly.Word
            , LLVM.ConstantOperand
                LLVM.Constant.Int
                  { integerBits = wordBits
                  , integerValue = int
                  }
            )

assembleOperandAndCastTo :: Assembly.Type -> Assembly.Operand -> Assembler LLVM.Operand
assembleOperandAndCastTo desiredType operand = do
  (nameSuggestion, type_, operand') <- assembleOperand operand
  cast nameSuggestion desiredType type_ operand'

cast :: Assembly.NameSuggestion -> Assembly.Type -> Assembly.Type -> LLVM.Operand -> Assembler LLVM.Operand
cast nameSuggestion newType type_ operand
  | type_ == newType =
    pure operand
  | otherwise =
    case (type_, newType) of
      (Assembly.Word, _) -> do
        newOperand <- freshName $ nameSuggestion <> "_pointer"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.IntToPtr
              { operand0 = operand
              , type' = llvmNewType
              , metadata = mempty
              }
        pure $ LLVM.LocalReference llvmNewType newOperand
      (_, Assembly.Word) -> do
        newOperand <- freshName $ nameSuggestion <> "_integer"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.PtrToInt
              { operand0 = operand
              , type' = llvmNewType
              , metadata = mempty
              }
        pure $ LLVM.LocalReference llvmNewType newOperand
      (Assembly.Struct types, Assembly.Struct newTypes) -> do
        let llvmType_ = llvmType type_
            go (index, struct) (fieldType, newFieldType) = do
              field <- freshName "field"
              let fieldOperand = LLVM.LocalReference (llvmType fieldType) field
              emitInstruction $
                field
                  LLVM.:= LLVM.ExtractValue
                    { aggregate = operand
                    , indices' = [index]
                    , metadata = mempty
                    }
              castField <- cast "field" newFieldType fieldType fieldOperand
              struct' <- freshName "struct"
              emitInstruction $
                struct'
                  LLVM.:= LLVM.InsertValue
                    { aggregate = struct
                    , element = castField
                    , indices' = [index]
                    , metadata = mempty
                    }
              pure (index + 1, LLVM.LocalReference llvmType_ struct')

        snd <$> foldM go (0, LLVM.ConstantOperand $ LLVM.Constant.Undef {constantType = llvmType_}) (zip types newTypes)
      _ -> do
        newOperand <- freshName $ nameSuggestion <> "_cast"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.BitCast
              { operand0 = operand
              , type' = llvmNewType
              , metadata = mempty
              }

        pure $ LLVM.LocalReference llvmNewType newOperand
  where
    llvmNewType = llvmType newType
