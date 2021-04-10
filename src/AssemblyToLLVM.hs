{-# LANGUAGE DuplicateRecordFields #-}
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
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified LLVM.AST as LLVM
import qualified LLVM.AST.CallingConvention as LLVM.CallingConvention
import qualified LLVM.AST.Constant as LLVM.Constant
import qualified LLVM.AST.Global as LLVM.Global
import qualified LLVM.AST.Linkage as LLVM
import qualified LLVM.AST.Type as LLVM.Type
import qualified Literal
import qualified Name
import Protolude hiding (IntMap, cast, local, moduleName)
import Representation (Representation)
import qualified Representation

type Assembler = State AssemblerState

data AssemblerState = AssemblerState
  { _locals :: HashMap Assembly.Local (LLVM.Operand, OperandType)
  , _usedGlobals :: HashMap LLVM.Name LLVM.Global
  , _usedNames :: HashMap ShortByteString Int
  , _instructions :: Tsil (LLVM.Named LLVM.Instruction)
  , _basicBlockName :: LLVM.Name
  , _basicBlocks :: Tsil LLVM.BasicBlock
  }

data OperandType
  = Word
  | WordPointer
  | FunctionPointer !Assembly.Return !Int
  deriving (Eq, Show)

globalOperandType :: Representation -> OperandType
globalOperandType representation =
  case representation of
    Representation.Empty ->
      WordPointer
    Representation.Direct _ ->
      Word
    Representation.Indirect _ ->
      WordPointer

llvmType :: OperandType -> LLVM.Type
llvmType type_ =
  case type_ of
    Word ->
      wordSizedInt
    WordPointer ->
      wordPointer
    FunctionPointer return_ numArgs ->
      LLVM.Type.ptr
        LLVM.FunctionType
          { resultType = returnLLVMType return_
          , argumentTypes = replicate numArgs wordPointer
          , isVarArg = False
          }

resultLLVMType :: Assembly.Result -> LLVM.Type
resultLLVMType result =
  case result of
    Assembly.Void -> LLVM.Type.void
    Assembly.NonVoid _ -> wordPointer

returnLLVMType :: Assembly.Return -> LLVM.Type
returnLLVMType result =
  case result of
    Assembly.ReturnsVoid -> LLVM.Type.void
    Assembly.Returns -> wordPointer

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
  pure $ LLVM.Name $ if i == 0 then bsName else bsName <> "$$" <> ShortByteString.toShort (toUtf8 (show i :: Text))

activateLocal :: OperandType -> Assembly.Local -> Assembler LLVM.Name
activateLocal type_ local@(Assembly.Local _ nameSuggestion) = do
  name <- freshName nameSuggestion
  modify $ \s ->
    s
      { _locals = HashMap.insert local (LLVM.LocalReference (llvmType type_) name, type_) $ _locals s
      }
  pure name

use :: LLVM.Global -> Assembler ()
use global =
  modify $ \s ->
    s
      { _usedGlobals = HashMap.insert (LLVM.Global.name global) global $ _usedGlobals s
      }

-------------------------------------------------------------------------------

assembleModule :: Name.Module -> [(Name.Lifted, Assembly.Definition Assembly.BasicBlock)] -> LLVM.Module
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

assembleDefinition :: Name.Lifted -> Assembly.Definition Assembly.BasicBlock -> ([LLVM.Global], HashMap LLVM.Name LLVM.Global)
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
        Assembly.KnownConstantDefinition representation (Literal.Integer value) isConstant -> do
          let type_ = llvmType $ globalOperandType representation
          pure
            [ LLVM.globalVariableDefaults
                { LLVM.Global.name = assembleName name
                , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
                , LLVM.Global.type' = type_
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
        Assembly.ConstantDefinition representation parameters basicBlock -> do
          parameters' <- mapM (activateLocal WordPointer) parameters
          assembleBasicBlockReturningResult basicBlock
          basicBlocks <- gets _basicBlocks
          let type_ =
                llvmType $ globalOperandType representation
          pure
            [ LLVM.globalVariableDefaults
                { LLVM.Global.name = assembleName name
                , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
                , LLVM.Global.type' = type_
                , LLVM.Global.initializer = Just LLVM.Constant.Undef {constantType = type_}
                , LLVM.Global.linkage = linkage
                }
            , LLVM.Global.functionDefaults
                { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
                , LLVM.Global.returnType = wordPointer
                , LLVM.Global.name = assembleName $ ClosureConvertedToAssembly.initDefinitionName name
                , LLVM.Global.parameters = ([LLVM.Parameter wordPointer parameter [] | parameter <- parameters'], False)
                , LLVM.Global.alignment = alignment
                , LLVM.Global.basicBlocks = toList basicBlocks
                , LLVM.Global.linkage = LLVM.Private
                }
            ]
        Assembly.FunctionDefinition parameters basicBlock@(Assembly.BasicBlock _ result) -> do
          parameters' <- mapM (activateLocal WordPointer) parameters
          assembleBasicBlockReturningResult basicBlock
          basicBlocks <- gets _basicBlocks
          pure
            [ LLVM.Global.functionDefaults
                { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
                , LLVM.Global.returnType = resultLLVMType result
                , LLVM.Global.name = assembleName name
                , LLVM.Global.parameters = ([LLVM.Parameter wordPointer parameter [] | parameter <- parameters'], False)
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

assembleBasicBlockReturningResult :: Assembly.BasicBlock -> Assembler ()
assembleBasicBlockReturningResult (Assembly.BasicBlock instructions result) = do
  blockName <- freshName "start"
  startBlock blockName
  mapM_ assembleInstruction instructions
  returnResult result

returnResult :: Assembly.Result -> Assembler ()
returnResult result = do
  case result of
    Assembly.Void -> do
      endBlock $ LLVM.Do LLVM.Ret {returnOperand = Nothing, metadata' = mempty}
    Assembly.NonVoid res -> do
      operand <- assembleOperand WordPointer res
      endBlock $ LLVM.Do LLVM.Ret {returnOperand = Just operand, metadata' = mempty}

assembleInstruction :: Assembly.Instruction Assembly.BasicBlock -> Assembler ()
assembleInstruction instruction =
  case instruction of
    Assembly.Copy destination source size -> do
      destination' <- assembleOperand WordPointer destination
      source' <- assembleOperand WordPointer source
      size' <- assembleOperand Word size
      destination'' <- freshName "destination"
      source'' <- freshName "source"
      let memcpyName =
            LLVM.Name $ "llvm.memcpy.p0i8.p0i8.i" <> fromString (show (wordBits :: Int))

          memcpyResultType =
            LLVM.Type.void

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
    Assembly.Call (Assembly.NonVoid destination) function arguments -> do
      function' <- assembleOperand (FunctionPointer Assembly.Returns $ length arguments) function
      arguments' <- mapM (assembleOperand WordPointer) arguments
      destination' <- activateLocal WordPointer destination
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
      function' <- assembleOperand (FunctionPointer Assembly.ReturnsVoid $ length arguments) function
      arguments' <- mapM (assembleOperand WordPointer) arguments
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
      address' <- assembleOperand WordPointer address
      destination' <- activateLocal Word destination
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
      address' <- assembleOperand WordPointer address
      value' <- assembleOperand Word value
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
    Assembly.InitGlobal global representation value -> do
      let type_ =
            globalOperandType representation

          storeIt = do
            value' <- assembleOperand type_ value
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
      case representation of
        Representation.Empty ->
          pure ()
        Representation.Direct _ ->
          storeIt
        Representation.Indirect _ ->
          storeIt
    Assembly.Add destination operand1 operand2 -> do
      operand1' <- assembleOperand Word operand1
      operand2' <- assembleOperand Word operand2
      destination' <- activateLocal Word destination
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
      operand1' <- assembleOperand Word operand1
      operand2' <- assembleOperand Word operand2
      destination' <- activateLocal Word destination
      emitInstruction $
        destination'
          LLVM.:= LLVM.Sub
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
    Assembly.StackAllocate destination size -> do
      destination' <- activateLocal WordPointer destination
      destination'' <- freshName "destination"
      size' <- assembleOperand Word size
      emitInstruction $
        destination''
          LLVM.:= LLVM.Alloca
            { numElements = Just size'
            , allocatedType = LLVM.Type.i8
            , alignment = alignment
            , metadata = mempty
            }
      emitInstruction $
        destination'
          LLVM.:= LLVM.BitCast
            { operand0 = LLVM.LocalReference bytePointer destination''
            , type' = wordPointer
            , metadata = mempty
            }
    Assembly.SaveStack destination -> do
      destination' <- activateLocal WordPointer destination
      destination'' <- freshName "destination"
      let stackSaveName =
            LLVM.Name "llvm.stacksave"

          stackSaveResultType =
            bytePointer

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
      operand' <- assembleOperand WordPointer operand
      operand'' <- freshName "operand"
      let stackRestoreName =
            LLVM.Name "llvm.stackrestore"

          stackRestoreResultType =
            LLVM.Type.void

          stackRestoreArgumentTypes =
            [bytePointer]

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
    Assembly.HeapAllocate {} ->
      panic "AssemblyToLLVM: HeapAllocate" -- TODO
    Assembly.Switch destination scrutinee branches (Assembly.BasicBlock defaultBranchInstructions defaultBranchResult) -> do
      scrutinee' <- assembleOperand Word scrutinee
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
        resultOperand <- forM result $ assembleOperand WordPointer
        endBlock $ LLVM.Do LLVM.Br {dest = afterSwitchLabel, metadata' = mempty}
        pure resultOperand
      startBlock defaultBranchLabel
      mapM_ assembleInstruction defaultBranchInstructions
      endBlock $ LLVM.Do LLVM.Br {dest = afterSwitchLabel, metadata' = mempty}
      defaultResultOperand <- forM defaultBranchResult $ assembleOperand WordPointer
      startBlock afterSwitchLabel
      case destination of
        Assembly.Void ->
          pure ()
        Assembly.NonVoid destinationLocal -> do
          destination' <- activateLocal WordPointer destinationLocal
          let voidedIncomingValues =
                (defaultResultOperand, defaultBranchLabel) : zip branchResultOperands (snd <$> branchLabels)
              incomingValues =
                case traverse (bitraverse identity pure) voidedIncomingValues of
                  Assembly.NonVoid incomingValues_ -> incomingValues_
                  Assembly.Void -> panic "AssemblyToLLVM: Switch with mismatch between instruction result and branch results"
          emitInstruction $
            destination'
              LLVM.:= LLVM.Phi
                { type' = llvmType WordPointer
                , incomingValues = incomingValues
                , metadata = mempty
                }

assembleOperand :: OperandType -> Assembly.Operand -> Assembler LLVM.Operand
assembleOperand type_ operand =
  case operand of
    Assembly.LocalOperand local@(Assembly.Local _ nameSuggestion) -> do
      locals <- gets _locals
      cast nameSuggestion type_ $ HashMap.lookupDefault (panic $ "assembleOperand: no such local " <> show local) local locals
    Assembly.GlobalConstant global representation -> do
      let globalName =
            assembleName global

          globalNameText =
            Assembly.nameText global

          nameSuggestion =
            Assembly.NameSuggestion globalNameText

          globalType =
            llvmType $ globalOperandType representation
      case representation of
        Representation.Empty -> do
          cast nameSuggestion type_ (LLVM.ConstantOperand $ LLVM.Constant.Null (LLVM.Type.ptr globalType), WordPointer)
        Representation.Direct containsHeapPointers -> do
          use
            LLVM.globalVariableDefaults
              { LLVM.Global.name = globalName
              , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
              , LLVM.Global.isConstant = True
              , LLVM.Global.type' = globalType
              }
          cast nameSuggestion type_ (LLVM.ConstantOperand $ LLVM.Constant.GlobalReference (LLVM.Type.ptr globalType) globalName, WordPointer)
        Representation.Indirect containsHeapPointers -> do
          use
            LLVM.globalVariableDefaults
              { LLVM.Global.name = globalName
              , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
              , LLVM.Global.isConstant = True
              , LLVM.Global.type' = globalType
              }
          destination <- freshName nameSuggestion
          emitInstruction $
            destination
              LLVM.:= LLVM.Load
                { volatile = False
                , address = LLVM.ConstantOperand $ LLVM.Constant.GlobalReference (LLVM.Type.ptr globalType) globalName
                , maybeAtomicity = Nothing
                , alignment = alignment
                , metadata = []
                }
          cast nameSuggestion type_ (LLVM.LocalReference (llvmType WordPointer) destination, WordPointer)
    Assembly.GlobalFunction global return_ arity -> do
      let defType =
            FunctionPointer return_ arity

          globalNameText =
            Assembly.nameText global

          nameSuggestion =
            Assembly.NameSuggestion globalNameText

          globalName =
            assembleName global

          globalType =
            llvmType defType

      use
        LLVM.functionDefaults
          { LLVM.Global.callingConvention = LLVM.CallingConvention.Fast
          , LLVM.Global.returnType = returnLLVMType return_
          , LLVM.Global.name = globalName
          , LLVM.Global.parameters = ([LLVM.Parameter wordPointer (LLVM.UnName parameter) [] | parameter <- [0 .. fromIntegral arity - 1]], False)
          , LLVM.Global.alignment = alignment
          }
      cast
        nameSuggestion
        type_
        ( LLVM.ConstantOperand $
            LLVM.Constant.GlobalReference globalType globalName
        , defType
        )
    Assembly.Lit lit ->
      case lit of
        Literal.Integer int ->
          cast
            "literal"
            type_
            ( LLVM.ConstantOperand
                LLVM.Constant.Int
                  { integerBits = wordBits
                  , integerValue = int
                  }
            , Word
            )

cast :: Assembly.NameSuggestion -> OperandType -> (LLVM.Operand, OperandType) -> Assembler LLVM.Operand
cast (Assembly.NameSuggestion nameSuggestion) newType (operand, type_)
  | type_ == newType =
    pure operand
  | otherwise =
    case (type_, newType) of
      (Word, _) -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_pointer"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.IntToPtr
              { operand0 = operand
              , type' = llvmType newType
              , metadata = mempty
              }
        pure $ LLVM.LocalReference (llvmType newType) newOperand
      (_, Word) -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_integer"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.PtrToInt
              { operand0 = operand
              , type' = llvmType newType
              , metadata = mempty
              }
        pure $ LLVM.LocalReference (llvmType newType) newOperand
      _ -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_cast"
        emitInstruction $
          newOperand
            LLVM.:= LLVM.BitCast
              { operand0 = operand
              , type' = llvmType newType
              , metadata = mempty
              }

        pure $ LLVM.LocalReference (llvmType newType) newOperand
