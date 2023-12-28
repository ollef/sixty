{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoFieldSelectors #-}

module AssemblyToLLVM where

import qualified Assembly
import qualified ClosureConvertedToAssembly
import Data.Bitraversable
import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString.Lazy as Lazy
import Data.ByteString.Short (ShortByteString)
import qualified Data.ByteString.Short as ShortByteString
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.String (fromString)
import qualified Literal
import qualified Name
import Protolude hiding (IntMap, cast, local)

newtype Name = Name {shortByteString :: ShortByteString}
  deriving (Eq, Show, Hashable, IsString)

localName :: Name -> Builder
localName (Name n) = "%" <> Builder.shortByteString n

globalName :: Name -> Builder
globalName (Name n) = "@" <> Builder.shortByteString n

data TypedOperand = TypedOperand {type_ :: !Builder, operand :: !Operand}
  deriving (Show)

typedOperand :: TypedOperand -> Builder
typedOperand TypedOperand {type_, operand = o} = type_ <> " " <> operand o

data Operand
  = Local !Name
  | Global !Name
  | Constant !Builder
  deriving (Show)

operand :: Operand -> Builder
operand = \case
  Local n -> localName n
  Global n -> globalName n
  Constant c -> c

separate :: Builder -> [Builder] -> Builder
separate separator = mconcat . intersperse separator

commaSeparate :: [Builder] -> Builder
commaSeparate = separate ", "

parens :: [Builder] -> Builder
parens bs = "(" <> commaSeparate bs <> ")"

braces :: [Builder] -> Builder
braces bs = "{" <> commaSeparate bs <> "}"

brackets :: [Builder] -> Builder
brackets bs = "[" <> commaSeparate bs <> "]"

type Assembler = State AssemblerState

data AssemblerState = AssemblerState
  { locals :: HashMap Assembly.Local (Assembly.Type, TypedOperand)
  , usedGlobals :: HashMap Name Builder
  , usedNames :: HashMap ShortByteString Int
  , instructions :: Builder
  , basicBlockName :: Name
  , basicBlocks :: Builder
  }

llvmType :: Assembly.Type -> Builder
llvmType type_ =
  case type_ of
    Assembly.Word -> wordSizedInt
    Assembly.WordPointer -> pointer
    Assembly.FunctionPointer _returnType _argumentTypes -> pointer

parameterAttributes :: Assembly.Type -> [Builder]
parameterAttributes type_ =
  case type_ of
    Assembly.Word -> []
    Assembly.WordPointer -> ["nonnull"]
    Assembly.FunctionPointer {} -> ["nonnull"]

llvmReturnType :: Assembly.Return Assembly.Type -> Builder
llvmReturnType result =
  case result of
    Assembly.Void -> "void"
    Assembly.Return type_ -> llvmType type_

alignment :: (Num a) => a
alignment = 8

wordBytes :: (Num a) => a
wordBytes = 8

wordBits :: (Num a) => a
wordBits = 64

wordSizedInt :: Builder
wordSizedInt = "i" <> Builder.intDec wordBits

pointer :: Builder
pointer = "ptr"

emitInstruction :: Builder -> Assembler ()
emitInstruction instruction =
  modify \s -> s {instructions = s.instructions <> "\n  " <> instruction}

startBlock :: Name -> Assembler ()
startBlock basicBlockName =
  modify \s -> s {basicBlockName}

endBlock :: Builder -> Assembler ()
endBlock terminator =
  modify \s ->
    s
      { instructions = mempty
      , basicBlockName = panic "AssemblyToLLVM: not in a basic block"
      , basicBlocks =
          s.basicBlocks
            <> "\n\n"
            <> Builder.shortByteString s.basicBlockName.shortByteString
            <> ":"
            <> s.instructions
            <> "\n  "
            <> terminator
      }

freshName :: Assembly.NameSuggestion -> Assembler Name
freshName (Assembly.NameSuggestion nameSuggestion) = do
  usedNames <- gets (.usedNames)
  let bsName = ShortByteString.toShort $ toUtf8 nameSuggestion
      i = HashMap.lookupDefault 0 bsName usedNames
  modify \s ->
    s
      { usedNames = HashMap.insert bsName (i + 1) usedNames
      }
  pure $ Name if i == 0 then bsName else bsName <> "$" <> ShortByteString.toShort (toUtf8 (show i :: Text))

activateLocal :: Assembly.Type -> Assembly.Local -> Assembler Name
activateLocal type_ local@(Assembly.Local _ nameSuggestion) = do
  name <- freshName nameSuggestion
  modify \s ->
    s
      { locals = HashMap.insert local (type_, TypedOperand {type_ = llvmType type_, operand = Local name}) s.locals
      }
  pure name

declare :: Name -> Builder -> Assembler ()
declare name decl =
  modify \s ->
    s {usedGlobals = HashMap.insert name decl s.usedGlobals}

-------------------------------------------------------------------------------
memset0 :: TypedOperand -> TypedOperand -> Assembler ()
memset0 destination size = do
  let memsetName = Name $ "llvm.memset.p0i8.i" <> fromString (show (wordBits :: Int))
  declare memsetName $
    "declare ccc void "
      <> globalName memsetName
      <> parens [pointer, "i8", wordSizedInt, "i1"]
  emitInstruction $
    "call ccc void "
      <> globalName memsetName
      <> parens
        [ destination.type_ <> " align " <> Builder.intDec alignment <> " " <> operand destination.operand
        , "i8 0"
        , typedOperand size
        , "i1 0"
        ]

-------------------------------------------------------------------------------

assembleModule :: [(Name.Lifted, Assembly.Definition)] -> Lazy.ByteString
assembleModule definitions = do
  let (assembledDefinitions, usedGlobals) =
        unzip $ foreach definitions $ uncurry assembleDefinition

      assembledDefinitions' =
        concat assembledDefinitions

      forwardDeclarations =
        HashMap.difference (mconcat usedGlobals) (HashSet.toMap $ HashSet.fromList $ fst <$> assembledDefinitions')

  Builder.toLazyByteString $
    separate "\n\n" $
      HashMap.elems forwardDeclarations <> map snd assembledDefinitions'

assembleDefinition :: Name.Lifted -> Assembly.Definition -> ([(Name, Builder)], HashMap Name Builder)
assembleDefinition name@(Name.Lifted _ liftedNameNumber) definition =
  second (.usedGlobals) $
    flip
      runState
      AssemblerState
        { locals = mempty
        , usedNames = mempty
        , usedGlobals = mempty
        , instructions = mempty
        , basicBlocks = mempty
        , basicBlockName = panic "AssemblyToLLVM: not in a basic block"
        }
      case definition of
        Assembly.KnownConstantDefinition type_ (Literal.Integer value) isConstant -> do
          let type' = llvmType type_
          pure
            [
              ( name'
              , globalName name'
                  <> " = unnamed_addr "
                  <> linkage
                  <> (if isConstant then "constant " else "global ")
                  <> type'
                  <> " "
                  <> Builder.integerDec value
              )
            ]
        Assembly.ConstantDefinition type_ functionReturnType parameters basicBlock -> do
          let type' = llvmType type_
              initName = assembleName $ ClosureConvertedToAssembly.initDefinitionName name
          parameters' <- mapM (uncurry activateLocal) parameters
          assembleBasicBlockReturningResult functionReturnType basicBlock
          basicBlocks <- gets (.basicBlocks)
          pure
            [
              ( name'
              , globalName name' <> " = unnamed_addr " <> linkage <> "global " <> type' <> " undef"
              )
            ,
              ( initName
              , "define private fastcc "
                  <> llvmReturnType functionReturnType
                  <> " "
                  <> globalName initName
                  <> parens [typedOperand TypedOperand {type_ = pointer, operand = Local p} | p <- parameters']
                  <> " align "
                  <> Builder.intDec alignment
                  <> " {"
                  <> basicBlocks
                  <> "\n}"
              )
            ]
        Assembly.FunctionDefinition returnType parameters basicBlock -> do
          parameters' <- mapM (uncurry activateLocal) parameters
          assembleBasicBlockReturningResult returnType basicBlock
          basicBlocks <- gets (.basicBlocks)
          pure
            [
              ( name'
              , "define "
                  <> linkage
                  <> "fastcc "
                  <> llvmReturnType returnType
                  <> " "
                  <> globalName (assembleName name)
                  <> parens
                    [ separate
                      " "
                      ( concat
                          [ [llvmType type_]
                          , parameterAttributes type_
                          , [localName parameter]
                          ]
                      )
                    | ((type_, _), parameter) <- zip parameters parameters'
                    ]
                  <> " align "
                  <> Builder.intDec alignment
                  <> " {"
                  <> basicBlocks
                  <> "\n}"
              )
            ]
  where
    name' = assembleName name
    linkage =
      case liftedNameNumber of
        0 ->
          ""
        _ ->
          "private "

assembleName :: Name.Lifted -> Name
assembleName =
  Name . ShortByteString.toShort . toUtf8 . Assembly.nameText

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
      endBlock "ret void"
    (Assembly.Return type_, Assembly.Return res) -> do
      res' <- assembleOperandAndCastTo type_ res
      endBlock $ "ret " <> typedOperand res'
    _ ->
      panic "AssemblyToLLVM.returnResult: return type mismatch"

assembleInstruction :: Assembly.Instruction -> Assembler ()
assembleInstruction instruction =
  case instruction of
    Assembly.Copy destination source size -> do
      destination' <- assembleOperandAndCastTo Assembly.WordPointer destination
      source' <- assembleOperandAndCastTo Assembly.WordPointer source
      size' <- assembleOperandAndCastTo Assembly.Word size
      let memcpyName = Name $ "llvm.memcpy.p0i8.p0i8.i" <> fromString (show (wordBits :: Int))
      declare memcpyName $
        "declare ccc void "
          <> globalName memcpyName
          <> parens [pointer, pointer, wordSizedInt, "i32", "i1"]
      let isVolatile = "i1 0"
      emitInstruction $
        "call ccc void "
          <> globalName memcpyName
          <> parens
            [ typedOperand destination'
            , typedOperand source'
            , typedOperand size'
            , typedOperand TypedOperand {type_ = "i32", operand = Constant $ Builder.intDec alignment}
            , isVolatile
            ]
    Assembly.Call (Assembly.Return (returnType, destination)) function arguments -> do
      function' <- assembleOperandAndCastTo (Assembly.FunctionPointer (Assembly.Return returnType) $ fst <$> arguments) function
      arguments' <- mapM (uncurry assembleOperandAndCastTo) arguments
      destination' <- activateLocal returnType destination
      emitInstruction $ localName destination' <> " = call fastcc " <> llvmType returnType <> " " <> operand function'.operand <> parens (typedOperand <$> arguments')
    Assembly.Call Assembly.Void function arguments -> do
      function' <- assembleOperandAndCastTo (Assembly.FunctionPointer Assembly.Void $ fst <$> arguments) function
      arguments' <- mapM (uncurry assembleOperandAndCastTo) arguments
      emitInstruction $ "call fastcc void " <> operand function'.operand <> parens (typedOperand <$> arguments')
    Assembly.Load destination address -> do
      address' <- assembleOperandAndCastTo Assembly.WordPointer address
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        localName destination'
          <> " = load "
          <> commaSeparate [wordSizedInt, typedOperand address', "align " <> Builder.intDec alignment]
    Assembly.Store address value -> do
      address' <- assembleOperandAndCastTo Assembly.WordPointer address
      value' <- assembleOperandAndCastTo Assembly.Word value
      emitInstruction $
        "store "
          <> commaSeparate
            [ typedOperand value'
            , typedOperand address'
            , "align " <> Builder.intDec alignment
            ]
    Assembly.InitGlobal global type_ value -> do
      value' <- assembleOperandAndCastTo type_ value
      emitInstruction $
        "store "
          <> commaSeparate
            [ typedOperand value'
            , typedOperand TypedOperand {type_ = pointer, operand = Global $ assembleName global}
            , "align " <> Builder.intDec alignment
            ]
    Assembly.Add destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        localName destination'
          <> " = add "
          <> typedOperand operand1'
          <> ", "
          <> operand operand2'.operand
    Assembly.Sub destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        localName destination'
          <> " = sub "
          <> typedOperand operand1'
          <> ", "
          <> operand operand2'.operand
    Assembly.Mul destination operand1 operand2 -> do
      operand1' <- assembleOperandAndCastTo Assembly.Word operand1
      operand2' <- assembleOperandAndCastTo Assembly.Word operand2
      destination' <- activateLocal Assembly.Word destination
      emitInstruction $
        localName destination'
          <> " = mul "
          <> typedOperand operand1'
          <> ", "
          <> operand operand2'.operand
    Assembly.AddPointer destination pointerOperand wordOperand -> do
      pointerOperand' <- assembleOperandAndCastTo Assembly.WordPointer pointerOperand
      wordOperand' <- assembleOperandAndCastTo Assembly.Word wordOperand
      destination' <- activateLocal Assembly.WordPointer destination
      -- TODO can this be inbounds?
      emitInstruction $
        localName destination' <> " = getelementptr i8, " <> typedOperand pointerOperand' <> ", " <> typedOperand wordOperand'
    Assembly.StackAllocate destination size -> do
      destination' <- activateLocal Assembly.WordPointer destination
      size' <- assembleOperandAndCastTo Assembly.Word size
      emitInstruction $ localName destination' <> " = alloca i8, " <> typedOperand size' <> ", align " <> Builder.intDec alignment
      memset0 TypedOperand {type_ = pointer, operand = Local destination'} size'
    Assembly.SaveStack destination -> do
      destination' <- activateLocal Assembly.WordPointer destination
      declare "llvm.stacksave" "declare ccc ptr @llvm.stacksave()"
      emitInstruction $ localName destination' <> " = call ccc ptr @llvm.stacksave()"
    Assembly.RestoreStack argument -> do
      argument' <- assembleOperandAndCastTo Assembly.WordPointer argument
      declare "llvm.stackrestore" $ "declare ccc void @llvm.stackrestore" <> parens [pointer]
      emitInstruction $ "call ccc void @llvm.stackrestore" <> parens [typedOperand argument']
    Assembly.HeapAllocate {destination, constructorTag, size} -> do
      destination' <- activateLocal Assembly.WordPointer destination
      size' <- assembleOperandAndCastTo Assembly.Word size
      declare
        "__regcall3__heap_alloc"
        $ "declare x86_regcallcc "
          <> wordSizedInt
          <> " @__regcall3__heap_alloc"
          <> parens ["i8", wordSizedInt]
      emitInstruction $
        localName destination'
          <> " = call x86_regcallcc "
          <> wordSizedInt
          <> "@__regcall3__heap_alloc"
          <> parens
            [ "i8 " <> Builder.word8Dec constructorTag
            , typedOperand size'
            ]
    Assembly.Retains ptr size -> _
    Assembly.Releases ptr size -> _
    Assembly.AllocateGlobal dst size -> _
    Assembly.ExtractHeapPointer destination pointer_ -> do
      destination' <- activateLocal Assembly.WordPointer destination
      pointer' <- assembleOperandAndCastTo Assembly.Word pointer_
      declare "heap_object_pointer" $ "declare ccc ptr @heap_object_pointer" <> parens [wordSizedInt]
      emitInstruction $ localName destination' <> " = call ccc ptr @heap_object_pointer" <> parens [typedOperand pointer']
    Assembly.ExtractHeapPointerConstructorTag destination pointer_ -> do
      destination' <- activateLocal Assembly.Word destination
      pointer' <- assembleOperandAndCastTo Assembly.Word pointer_
      declare "heap_object_constructor_tag" $ "declare ccc " <> wordSizedInt <> "@heap_object_constructor_tag" <> parens [wordSizedInt]
      emitInstruction $
        localName destination'
          <> " = call ccc "
          <> wordSizedInt
          <> " @heap_object_constructor_tag"
          <> parens [typedOperand pointer']
    Assembly.Switch destination scrutinee branches (Assembly.BasicBlock defaultBranchInstructions defaultBranchResult) -> do
      scrutinee' <- assembleOperandAndCastTo Assembly.Word scrutinee
      branchLabels <- forM branches \(i, _) -> do
        branchLabel <- freshName $ Assembly.NameSuggestion $ "branch_" <> show i
        pure (i, branchLabel)
      defaultBranchLabel <- freshName "default"
      afterSwitchLabel <- freshName "after_switch"
      endBlock $
        "switch "
          <> typedOperand scrutinee'
          <> ", label "
          <> localName defaultBranchLabel
          <> " "
          <> brackets [separate " " [typedOperand TypedOperand {type_ = wordSizedInt, operand = Constant $ Builder.integerDec i} <> ", label " <> localName l | (i, l) <- branchLabels]]
      branchResultOperands <- forM (zip branchLabels branches) \((_, branchLabel), (_, Assembly.BasicBlock instructions result)) -> do
        startBlock branchLabel
        mapM_ assembleInstruction instructions
        resultOperand <- forM ((,) . fst <$> destination <*> result) $ uncurry assembleOperandAndCastTo
        branchLabel' <- gets (.basicBlockName)
        endBlock $ "br label " <> localName afterSwitchLabel
        pure (resultOperand, branchLabel')
      startBlock defaultBranchLabel
      mapM_ assembleInstruction defaultBranchInstructions
      defaultResultOperand <- forM ((,) . fst <$> destination <*> defaultBranchResult) $ uncurry assembleOperandAndCastTo
      defaultBranchLabel' <- gets (.basicBlockName)
      endBlock $ "br label " <> localName afterSwitchLabel
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
            localName destination'
              <> " = phi "
              <> llvmType destinationType
              <> " "
              <> commaSeparate [brackets [operand v.operand, localName l] | (v, l) <- incomingValues]

assembleOperand :: Assembly.Operand -> Assembler (Assembly.NameSuggestion, Assembly.Type, TypedOperand)
assembleOperand = \case
  Assembly.LocalOperand local@(Assembly.Local _ nameSuggestion) -> do
    locals <- gets (.locals)
    let (type_, operand') = HashMap.lookupDefault (panic $ "assembleOperandWithOperandType: no such local " <> show local) local locals
    pure (nameSuggestion, type_, operand')
  Assembly.GlobalConstant global globalType -> do
    let globalName_ = assembleName global
        globalNameText = Assembly.nameText global
        nameSuggestion = Assembly.NameSuggestion globalNameText
    declare globalName_ $ globalName globalName_ <> " = external constant " <> llvmType globalType
    case globalType of
      Assembly.Word ->
        pure (nameSuggestion, Assembly.WordPointer, TypedOperand {type_ = pointer, operand = Global globalName_})
      Assembly.WordPointer -> do
        destination <- freshName nameSuggestion
        emitInstruction $
          localName destination <> " = load " <> wordSizedInt <> ", ptr " <> globalName globalName_ <> ", align " <> Builder.intDec alignment
        pure (nameSuggestion, Assembly.WordPointer, TypedOperand {type_ = wordSizedInt, operand = Local destination})
      Assembly.FunctionPointer _ _ -> do
        let llvmType_ = llvmType globalType
        destination <- freshName nameSuggestion
        emitInstruction $
          localName destination <> " = load " <> llvmType_ <> ", ptr " <> globalName globalName_ <> ", align " <> Builder.intDec alignment
        pure (nameSuggestion, Assembly.WordPointer, TypedOperand {type_ = llvmType_, operand = Local destination})
  Assembly.GlobalFunction global returnType parameterTypes -> do
    let defType = Assembly.FunctionPointer returnType parameterTypes
        globalNameText = Assembly.nameText global
        nameSuggestion = Assembly.NameSuggestion globalNameText
        globalName_ = assembleName global
        globalType = llvmType defType
    declare globalName_ $ "declare fastcc " <> llvmReturnType returnType <> " " <> globalName globalName_ <> parens (llvmType <$> parameterTypes)
    pure (nameSuggestion, defType, TypedOperand {type_ = globalType, operand = Global globalName_})
  Assembly.Lit lit ->
    case lit of
      Literal.Integer int ->
        pure
          ( "literal"
          , Assembly.Word
          , TypedOperand {type_ = wordSizedInt, operand = Constant $ Builder.integerDec int}
          )

assembleOperandAndCastTo :: Assembly.Type -> Assembly.Operand -> Assembler TypedOperand
assembleOperandAndCastTo desiredType op = do
  (nameSuggestion, type_, operand') <- assembleOperand op
  cast nameSuggestion desiredType type_ operand'

cast :: Assembly.NameSuggestion -> Assembly.Type -> Assembly.Type -> TypedOperand -> Assembler TypedOperand
cast nameSuggestion newType type_ operand_
  | type_ == newType =
      pure operand_
  | otherwise =
      case (type_, newType) of
        (Assembly.Word, _) -> do
          newOperand <- freshName $ nameSuggestion <> "_pointer"
          emitInstruction $
            localName newOperand <> " = inttoptr " <> wordSizedInt <> " " <> typedOperand operand_ <> " to ptr "
          pure TypedOperand {type_ = llvmNewType, operand = Local newOperand}
        (_, Assembly.Word) -> do
          newOperand <- freshName $ nameSuggestion <> "_integer"
          emitInstruction $
            localName newOperand <> " = ptrtoint " <> typedOperand operand_ <> " to " <> llvmNewType
          pure TypedOperand {type_ = llvmNewType, operand = Local newOperand}
        _ -> do
          newOperand <- freshName $ nameSuggestion <> "_cast"
          emitInstruction $
            localName newOperand <> " = bitcast " <> typedOperand operand_ <> " to " <> llvmNewType
          pure TypedOperand {type_ = llvmNewType, operand = Local newOperand}
  where
    llvmNewType = llvmType newType
