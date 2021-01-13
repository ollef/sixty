{-# language DuplicateRecordFields #-}
{-# language OverloadedStrings #-}
{-# options_ghc -Wno-incomplete-record-updates #-}
module CPSAssemblyToLLVM where

import qualified Assembly
import qualified ClosureConvertedToAssembly
import qualified CPSAssembly
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as ShortByteString
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.String (fromString)
import Data.Text.Prettyprint.Doc
import qualified Literal
import qualified LLVM.AST as LLVM
import qualified LLVM.AST.CallingConvention as LLVM.CallingConvention
import qualified LLVM.AST.Constant as LLVM.Constant
import qualified LLVM.AST.Global as LLVM.Global
import qualified LLVM.AST.Linkage as LLVM
import qualified LLVM.AST.ParameterAttribute as ParameterAttribute
import qualified LLVM.AST.Type as LLVM.Type
import qualified Name
import Protolude hiding (IntMap, cast, local, moduleName)

type Assembler = State AssemblerState

data AssemblerState = AssemblerState
  { _locals :: HashMap Assembly.Local (LLVM.Operand, OperandType)
  , _usedGlobals :: HashMap LLVM.Name LLVM.Global
  , _usedNames :: HashMap ShortByteString Int
  }

data OperandType
  = Word
  | WordPointer
  | FunctionPointer !Int
  deriving (Eq, Show)

llvmType :: OperandType -> LLVM.Type
llvmType type_ =
  case type_ of
     Word ->
       wordSizedInt

     WordPointer ->
       wordPointer

     FunctionPointer numArgs ->
       LLVM.Type.ptr LLVM.FunctionType
         { resultType = LLVM.VoidType
         , argumentTypes = replicate numArgs wordPointer
         , isVarArg = False
         }

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

freshName :: Assembly.NameSuggestion -> Assembler LLVM.Name
freshName (Assembly.NameSuggestion nameSuggestion) = do
  usedNames <- gets _usedNames
  let
    bsName =
      ShortByteString.toShort $ toUtf8 nameSuggestion

    i =
      HashMap.lookupDefault 0 bsName usedNames
  modify $ \s -> s
    { _usedNames = HashMap.insert bsName (i + 1) usedNames
    }
  pure $ LLVM.Name $ if i == 0 then bsName else bsName <> "$$" <> ShortByteString.toShort (toUtf8 (show i :: Text))

activateLocal :: OperandType -> Assembly.Local -> Assembler LLVM.Name
activateLocal type_ local@(Assembly.Local _ nameSuggestion) = do
  name <- freshName nameSuggestion
  modify $ \s -> s
    { _locals = HashMap.insert local (LLVM.LocalReference (llvmType type_) name, type_) $ _locals s
    }
  pure name

use :: LLVM.Global -> Assembler ()
use global =
  modify $ \s -> s
    { _usedGlobals = HashMap.insert (LLVM.Global.name global) global $ _usedGlobals s
    }

-------------------------------------------------------------------------------

assembleModule :: Name.Module -> [(Assembly.Name, CPSAssembly.Definition)] -> LLVM.Module
assembleModule (Name.Module moduleNameText) definitions = do
  let
    (assembledDefinitions, usedGlobals) =
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

assembleDefinition :: Assembly.Name -> CPSAssembly.Definition -> ([LLVM.Global], HashMap LLVM.Name LLVM.Global)
assembleDefinition name@(Assembly.Name liftedName@(Name.Lifted _ liftedNameNumber) nameNumber) definition =
  second _usedGlobals $
  flip runState AssemblerState
    { _locals = mempty
    , _usedNames = mempty
    , _usedGlobals = mempty
    } $
    case definition of
     Assembly.ConstantDefinition parameters basicBlock -> do
       parameters' <- mapM (activateLocal WordPointer) parameters
       basicBlocks <- assembleBasicBlock basicBlock
       pure
         [ LLVM.globalVariableDefaults
           { LLVM.Global.name = LLVM.Name $ assembleName name
           , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
           , LLVM.Global.type' = wordPointer
           , LLVM.Global.initializer = Just LLVM.Constant.Undef { constantType = wordPointer }
           , LLVM.Global.linkage = linkage
           }
         , LLVM.Global.functionDefaults
           { LLVM.Global.callingConvention = LLVM.CallingConvention.GHC
           , LLVM.Global.returnType = LLVM.VoidType
           , LLVM.Global.name = LLVM.Name $ assembleName $ Assembly.Name (ClosureConvertedToAssembly.initDefinitionName liftedName) nameNumber
           , LLVM.Global.parameters = ([LLVM.Parameter wordPointer parameter [] | parameter <- parameters'], False)
           , LLVM.Global.alignment = alignment
           , LLVM.Global.basicBlocks = basicBlocks
           , LLVM.Global.linkage = LLVM.Private
           }
         ]

     Assembly.FunctionDefinition parameters basicBlock -> do
       parameters' <- mapM (activateLocal WordPointer) parameters
       basicBlocks <- assembleBasicBlock basicBlock
       pure
         [ LLVM.Global.functionDefaults
           { LLVM.Global.callingConvention = LLVM.CallingConvention.GHC
           , LLVM.Global.returnType = LLVM.VoidType
           , LLVM.Global.name = LLVM.Name $ assembleName name
           , LLVM.Global.parameters = ([LLVM.Parameter wordPointer parameter [] | parameter <- parameters'], False)
           , LLVM.Global.alignment = alignment
           , LLVM.Global.basicBlocks = basicBlocks
           , LLVM.Global.linkage = linkage
           }
         ]
  where
    linkage =
      case (liftedNameNumber, nameNumber) of
        (0, 0) ->
          LLVM.External

        _ ->
          LLVM.Private

assembleName :: Assembly.Name -> ShortByteString
assembleName =
  ShortByteString.toShort . toUtf8 . Assembly.nameText

assembleBasicBlock :: CPSAssembly.BasicBlock -> Assembler [LLVM.BasicBlock]
assembleBasicBlock (CPSAssembly.BasicBlock instructions terminator) = do
  blockLabel <- freshName "block"
  compiledInstructions <- mapM assembleInstruction instructions
  assembleTerminator blockLabel (concat compiledInstructions) terminator

assembleTerminator :: LLVM.Name -> [LLVM.Named LLVM.Instruction] -> CPSAssembly.Terminator -> Assembler [LLVM.BasicBlock]
assembleTerminator blockLabel instructions terminator =
  case terminator of
    CPSAssembly.Switch scrutinee branches defaultBranch -> do
      (scrutinee', scrutineeInstructions) <- assembleOperand Word scrutinee
      branches' <- forM branches $ \(int, branchTerminator) -> do
        branchLabel <- freshName $ Assembly.NameSuggestion $ "branch_" <> show int
        blocks <- assembleTerminator branchLabel [] branchTerminator
        pure (int, branchLabel, blocks)
      defaultLabel <- freshName "default"
      defaultBlocks <- assembleTerminator defaultLabel [] defaultBranch
      pure $
        [ LLVM.BasicBlock
          blockLabel
          (scrutineeInstructions <> instructions)
          (LLVM.Do LLVM.Switch
            { operand0' = scrutinee'
            , defaultDest = defaultLabel
            , dests = [(LLVM.Constant.Int wordBits $ fromIntegral int, label) | (int, label, _) <- branches']
            , metadata' = []
            }
          )
        ]
        <> concat [blocks | (_, _, blocks) <- branches']
        <> defaultBlocks

    CPSAssembly.TailCall function arguments -> do
      (function', functionInstructions) <- assembleOperand (FunctionPointer $ length arguments) function
      (arguments', argumentInstructions) <- unzip <$> mapM (assembleOperand WordPointer) arguments
      pure
        [ LLVM.BasicBlock
          blockLabel
          (instructions <>
            functionInstructions <>
            concat argumentInstructions <>
            [ LLVM.Do LLVM.Call
              { tailCallKind = Just LLVM.Tail
              , callingConvention = LLVM.CallingConvention.GHC
              , returnAttributes = []
              , function = Right function'
              , arguments = [(arg, []) | arg <- arguments']
              , functionAttributes = []
              , metadata = []
              }
            ]
          )
          (LLVM.Do LLVM.Ret { returnOperand = Nothing, metadata' = mempty })
        ]

assembleInstruction :: CPSAssembly.Instruction -> Assembler [LLVM.Named LLVM.Instruction]
assembleInstruction instruction =
  case instruction of
    CPSAssembly.Copy destination source size -> do
      (destination', destinationInstructions) <- assembleOperand WordPointer destination
      (source', sourceInstructions) <- assembleOperand WordPointer source
      (size', sizeInstructions) <- assembleOperand Word size
      destination'' <- freshName "destination"
      source'' <- freshName "source"
      let
        memcpyName =
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
      use LLVM.functionDefaults
        { LLVM.Global.returnType = memcpyResultType
        , LLVM.Global.name = memcpyName
        , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0..] memcpyArgumentTypes], False)
        }
      pure $
        destinationInstructions <>
        sourceInstructions <>
        sizeInstructions <>
        [ destination'' LLVM.:=
            LLVM.BitCast
              { operand0 = destination'
              , type' = bytePointer
              , metadata = mempty
              }
        , source'' LLVM.:=
            LLVM.BitCast
              { operand0 = source'
              , type' = bytePointer
              , metadata = mempty
              }
        , LLVM.Do
          LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference memcpyType memcpyName
            , arguments = [(arg, []) | arg <- arguments]
            , functionAttributes = []
            , metadata = []
            }
        ]

    CPSAssembly.Load destination address -> do
      (address', addressInstructions) <- assembleOperand WordPointer address
      destination' <- activateLocal Word destination
      pure $
        addressInstructions <>
        [ destination' LLVM.:=
          LLVM.Load
            { volatile = False
            , address = address'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
        ]

    CPSAssembly.Store address value -> do
      (address', addressInstructions) <- assembleOperand WordPointer address
      (value', valueInstructions) <- assembleOperand Word value
      pure $
        addressInstructions <>
        valueInstructions <>
        [ LLVM.Do
          LLVM.Store
            { volatile = False
            , address = address'
            , value = value'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
        ]

    CPSAssembly.SetUndefined destination (Assembly.Lit (Literal.Integer size))
      | size == wordBytes -> do
        (address', addressInstructions) <- assembleOperand WordPointer destination
        pure $
          addressInstructions <>
          [ LLVM.Do
            LLVM.Store
              { volatile = False
              , address = address'
              , value = LLVM.ConstantOperand $ LLVM.Constant.Undef $ llvmType Word
              , maybeAtomicity = Nothing
              , alignment = alignment
              , metadata = []
              }
          ]

    CPSAssembly.SetUndefined destination size -> do
      (destination', destinationInstructions) <- assembleOperand WordPointer destination
      (size', sizeInstructions) <- assembleOperand Word size
      destination'' <- freshName "destination"
      let
        memsetResultType =
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
          [ (LLVM.LocalReference bytePointer destination'', [ParameterAttribute.Alignment alignment])
          , (LLVM.ConstantOperand $ LLVM.Constant.Undef LLVM.Type.i8, []) -- TODO is poison better (when using LLVM 12)?
          , (size', [])
          , (LLVM.ConstantOperand $ LLVM.Constant.Int 1 0, []) -- isvolatile
          ]

      use LLVM.functionDefaults
        { LLVM.Global.returnType = memsetResultType
        , LLVM.Global.name = memsetName
        , LLVM.Global.parameters = ([LLVM.Parameter type_ (LLVM.UnName parameter) [] | (parameter, type_) <- zip [0..] memsetArgumentTypes], False)
        }
      pure $
        destinationInstructions <>
        sizeInstructions <>
        [ destination'' LLVM.:=
            LLVM.BitCast
              { operand0 = destination'
              , type' = bytePointer
              , metadata = mempty
              }
        , LLVM.Do
          LLVM.Call
            { tailCallKind = Nothing
            , callingConvention = LLVM.CallingConvention.C
            , returnAttributes = []
            , function = Right $ LLVM.ConstantOperand $ LLVM.Constant.GlobalReference memsetType memsetName
            , arguments = arguments
            , functionAttributes = []
            , metadata = []
            }
        ]

    CPSAssembly.InitGlobal global value -> do
      (value', valueInstructions) <- assembleOperand WordPointer value
      pure $
        valueInstructions <>
        [ LLVM.Do
          LLVM.Store
            { volatile = False
            , address =
              LLVM.ConstantOperand $
              LLVM.Constant.GlobalReference
                (LLVM.Type.ptr $ llvmType WordPointer)
                (LLVM.Name $ assembleName $ Assembly.Name global 0)
            , value = value'
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
        ]

    CPSAssembly.Add destination operand1 operand2 -> do
      (operand1', operand1Instructions) <- assembleOperand Word operand1
      (operand2', operand2Instructions) <- assembleOperand Word operand2
      destination' <- activateLocal Word destination
      pure $
        operand1Instructions <>
        operand2Instructions <>
        [ destination' LLVM.:=
          LLVM.Add
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
        ]

    CPSAssembly.Sub destination operand1 operand2 -> do
      (operand1', operand1Instructions) <- assembleOperand Word operand1
      (operand2', operand2Instructions) <- assembleOperand Word operand2
      destination' <- activateLocal Word destination
      pure $
        operand1Instructions <>
        operand2Instructions <>
        [ destination' LLVM.:=
          LLVM.Sub
            { nsw = False
            , nuw = False
            , operand0 = operand1'
            , operand1 = operand2'
            , metadata = []
            }
        ]

    CPSAssembly.HeapAllocate {} ->
      panic "Assember: HeapAllocate" -- TODO

assembleOperand :: OperandType -> Assembly.Operand -> Assembler (LLVM.Operand, [LLVM.Named LLVM.Instruction])
assembleOperand type_ operand =
  case operand of
    Assembly.LocalOperand local@(Assembly.Local _ nameSuggestion) -> do
      locals <- gets _locals
      cast nameSuggestion type_ $ HashMap.lookupDefault (panic $ "assembleOperand: no such local " <> show local) local locals

    Assembly.GlobalConstant global -> do
      let
        globalNameText =
          Assembly.nameText global

        nameSuggestion =
          Assembly.NameSuggestion globalNameText

      destination <- freshName nameSuggestion
      (castDestination, castInstructions) <- cast nameSuggestion type_ (LLVM.LocalReference (llvmType WordPointer) destination, WordPointer)
      let
        globalName =
          LLVM.Name $ assembleName global

        globalType =
          llvmType WordPointer

      use LLVM.globalVariableDefaults
        { LLVM.Global.name = globalName
        , LLVM.Global.type' = globalType
        }
      pure
        ( castDestination
        , destination LLVM.:=
          LLVM.Load
            { volatile = False
            , address = LLVM.ConstantOperand $ LLVM.Constant.GlobalReference (LLVM.Type.ptr globalType) globalName
            , maybeAtomicity = Nothing
            , alignment = alignment
            , metadata = []
            }
          : castInstructions
        )

    Assembly.GlobalFunction global arity -> do
      let
        defType =
          FunctionPointer $ 1 + arity

        globalNameText =
          Assembly.nameText global

        nameSuggestion =
          Assembly.NameSuggestion globalNameText

        globalName =
          LLVM.Name $ assembleName global

        globalType =
          llvmType defType

      use LLVM.functionDefaults
        { LLVM.Global.callingConvention = LLVM.CallingConvention.GHC
        , LLVM.Global.returnType = LLVM.VoidType
        , LLVM.Global.name = globalName
        , LLVM.Global.parameters = ([LLVM.Parameter wordPointer (LLVM.UnName parameter) [] | parameter <- [0..fromIntegral arity]], False)
        , LLVM.Global.alignment = alignment
        }
      cast nameSuggestion type_
        ( LLVM.ConstantOperand $
          LLVM.Constant.GlobalReference globalType globalName
        , defType
        )

    Assembly.Lit lit ->
      case lit of
        Literal.Integer int ->
          cast "literal" type_
            ( LLVM.ConstantOperand LLVM.Constant.Int
              { integerBits = wordBits
              , integerValue = int
              }
            , Word
            )

cast :: Assembly.NameSuggestion -> OperandType -> (LLVM.Operand, OperandType) -> Assembler (LLVM.Operand, [LLVM.Named LLVM.Instruction])
cast (Assembly.NameSuggestion nameSuggestion) newType (operand, type_)
  | type_ == newType =
    pure (operand, [])

  | otherwise =
    case (type_, newType) of
      (Word, _) -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_pointer"
        pure
          ( LLVM.LocalReference (llvmType newType) newOperand
          , [ newOperand LLVM.:=
              LLVM.IntToPtr
                { operand0 = operand
                , type' = llvmType newType
                , metadata = mempty
                }
            ]
          )

      (_, Word) -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_integer"
        pure
          ( LLVM.LocalReference (llvmType newType) newOperand
          , [ newOperand LLVM.:=
              LLVM.PtrToInt
                { operand0 = operand
                , type' = llvmType newType
                , metadata = mempty
                }
            ]
          )

      _ -> do
        newOperand <- freshName $ Assembly.NameSuggestion $ nameSuggestion <> "_cast"
        pure
          ( LLVM.LocalReference (llvmType newType) newOperand
          , [ newOperand LLVM.:=
              LLVM.BitCast
                { operand0 = operand
                , type' = llvmType newType
                , metadata = mempty
                }
            ]
          )
