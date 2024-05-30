{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoFieldSelectors #-}

module LowToLLVM where

import Data.ByteString.Builder (Builder)
import qualified Data.ByteString.Builder as Builder
import qualified Data.ByteString.Lazy as Lazy
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Text.Encoding (encodeUtf8Builder)
import qualified Index.Seq
import qualified Index.Seq as Index (Seq)
import qualified Literal
import Low.PassBy (PassBy)
import qualified Low.PassBy as PassBy
import Low.Representation (Representation)
import qualified Low.Representation as Representation
import qualified Low.Syntax as Syntax
import Monad hiding (freshVar)
import Name (Name)
import qualified Name
import Prettyprinter (pretty)
import Protolude hiding (IntMap, cast, local, moduleName, repr)
import qualified Query
import Rock.Core

newtype Var = Var Text
  deriving (Eq, Ord, Show, Hashable)

nameBuilder :: Var -> Builder
nameBuilder (Var n) = encodeUtf8Builder n

varName :: Var -> Builder
varName n = "%" <> nameBuilder n

liftedName :: Name.Lifted -> Builder
liftedName = \case
  Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) 0 ->
    "@" <> encodeUtf8Builder moduleName <> "." <> encodeUtf8Builder name_
  Name.Lifted (Name.Qualified (Name.Module moduleName) (Name.Name name_)) i ->
    "@" <> encodeUtf8Builder moduleName <> "." <> encodeUtf8Builder name_ <> "$" <> Builder.intDec i

initName :: Name.Lifted -> Name.Lifted
initName (Name.Lifted (Name.Qualified m (Name.Name n)) i) =
  Name.Lifted (Name.Qualified m (Name.Name $ n <> "$init")) i

data Operand
  = Local !Var
  | Constant !Builder
  | ConstantReference !Builder !Builder
  deriving (Show)

operand :: Operand -> Builder
operand = \case
  Local v -> varName v
  Constant c -> c
  ConstantReference a b -> braces ["ptr " <> a, "ptr " <> b]

typedOperand :: (PassBy, Operand) -> Builder
typedOperand (passBy, o) =
  llvmType passBy <> " " <> operand o

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

wordSizedInt :: Builder
wordSizedInt = "i" <> Builder.intDec Representation.wordBits

type Assembler = StateT AssemblerState M

data AssemblerState = AssemblerState
  { usedGlobals :: HashSet Name.Lifted
  , usedLLVMGlobals :: HashMap Text Builder
  , usedLocals :: HashMap Var Int
  , instructions :: Builder
  , basicBlockName :: Var
  , basicBlocks :: Builder
  }

runAssembler :: Assembler a -> M (a, (HashSet Name.Lifted, HashMap Text Builder))
runAssembler =
  fmap (second (\s -> (s.usedGlobals, s.usedLLVMGlobals)))
    . flip
      runStateT
      AssemblerState
        { usedLocals = mempty
        , usedGlobals = mempty
        , usedLLVMGlobals = mempty
        , instructions = mempty
        , basicBlocks = mempty
        , basicBlockName = panic "AssemblyToLLVM: not in a basic block"
        }

llvmType :: PassBy -> Builder
llvmType = \case
  PassBy.Reference -> "{ptr, ptr}"
  PassBy.Value repr ->
    case (pointerType repr.pointers, nonPointerType repr.nonPointerBytes) of
      (Nothing, Nothing) -> "{}"
      (Just p, Nothing) -> p
      (Nothing, Just np) -> np
      (Just p, Just np) -> braces [p, np]

llvmReturnType :: PassBy -> Builder
llvmReturnType = \case
  PassBy.Value Representation.Empty -> "void"
  passBy -> llvmType passBy

pointerType :: Word32 -> Maybe Builder
pointerType = \case
  0 -> Nothing
  1 -> Just wordSizedInt
  n -> Just $ "[" <> Builder.word32Dec n <> " x " <> wordSizedInt <> "]"

nonPointerType :: Word32 -> Maybe Builder
nonPointerType = \case
  0 -> Nothing
  1 -> Just "i8"
  2 -> Just "i16"
  4 -> Just "i32"
  8 -> Just "i64"
  n -> Just $ "[" <> Builder.word32Dec n <> " x i8]"

emitInstruction :: Builder -> Assembler ()
emitInstruction instruction =
  modify \s -> s {instructions = s.instructions <> "\n  " <> instruction}

startBlock :: Var -> Assembler ()
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
            <> nameBuilder s.basicBlockName
            <> ":"
            <> s.instructions
            <> "\n  "
            <> terminator
      }

freshVar :: Name -> Assembler Var
freshVar (Name.Name nameText) = do
  usedLocals <- gets (.usedLocals)
  let (i, usedNames') =
        HashMap.alterF
          ( \case
              Nothing -> (0, Just 1)
              Just j -> (j, Just $ j + 1)
          )
          (Var nameText)
          usedLocals
  modify \s -> s {usedLocals = usedNames'}
  pure $ Var if i == 0 then nameText else nameText <> "$" <> (show i :: Text)

declareGlobal :: Name.Lifted -> Assembler ()
declareGlobal name =
  modify \s ->
    s {usedGlobals = HashSet.insert name s.usedGlobals}

declareLLVMGlobal :: Text -> Builder -> Assembler ()
declareLLVMGlobal name decl =
  modify \s ->
    s {usedLLVMGlobals = HashMap.insert name decl s.usedLLVMGlobals}

-------------------------------------------------------------------------------

saveStack :: Assembler Var
saveStack = do
  declareLLVMGlobal "llvm.stackrestore" "declare void @llvm.stackrestore(ptr)"
  var <- freshVar "stack"
  emitInstruction $ varName var <> " = call ptr @llvm.stacksave()"
  pure var

restoreStack :: Var -> Assembler ()
restoreStack var = do
  declareLLVMGlobal "llvm.stacksave" "declare ptr @llvm.stackesave()"
  emitInstruction $ "call void @llvm.stackrestore" <> parens ["ptr " <> varName var]

-------------------------------------------------------------------------------

assembleModule :: [(Name.Lifted, Syntax.Definition)] -> M Lazy.ByteString
assembleModule definitions = do
  (assembledDefinitions, allUsedGlobals) <-
    unzip <$> forM definitions (runAssembler . uncurry assembleDefinition)
  let (usedGlobals, usedLLVMGlobals) = bimap mconcat mconcat $ unzip allUsedGlobals
      assembledDefinitions' = concat assembledDefinitions
      externalGlobals = foldl' (flip HashSet.delete) usedGlobals $ fst <$> concat assembledDefinitions
  externalGlobalDeclarations <- mapM declaration $ HashSet.toList externalGlobals
  pure $
    Builder.toLazyByteString $
      separate "\n\n" $
        HashMap.elems usedLLVMGlobals <> externalGlobalDeclarations <> map snd assembledDefinitions'

declaration :: Name.Lifted -> M Builder
declaration global = do
  signature <- fetch $ Query.LowSignature global
  pure case signature of
    Syntax.FunctionSignature passParamsBy passReturnBy -> do
      let (passReturnBy', passParamsBy') = case passReturnBy of
            PassBy.Value _ -> (passReturnBy, passParamsBy)
            PassBy.Reference -> (PassBy.Value Representation.type_, PassBy.Reference : passParamsBy)
      "declare fastcc "
        <> llvmReturnType passReturnBy'
        <> " "
        <> liftedName global
        <> parens (llvmType <$> passParamsBy')
    Syntax.ConstantSignature repr ->
      liftedName global <> " = external global " <> llvmType (PassBy.Value repr)

type Environment v = Index.Seq v (PassBy, Operand)

assembleDefinition :: Name.Lifted -> Syntax.Definition -> Assembler [(Name.Lifted, Builder)]
assembleDefinition name definition =
  case definition of
    Syntax.FunctionDefinition function ->
      pure <$> assembleFunction name Index.Seq.Empty function
    Syntax.ConstantDefinition repr term ->
      assembleConstant name repr term

assembleFunction
  :: Name.Lifted
  -> Environment v
  -> Syntax.Function v
  -> Assembler (Name.Lifted, Builder)
assembleFunction functionName env = \case
  Syntax.Parameter name passBy function -> do
    var <- freshVar name
    assembleFunction functionName (env Index.Seq.:> (passBy, Local var)) function
  Syntax.Body passReturnBy term -> do
    let parameters = second fromLocal <$> Index.Seq.toSeq env
    entry <- freshVar "entry"
    startBlock entry
    (result, stack) <- assembleTerm env Nothing passReturnBy term
    mapM_ restoreStack stack
    endBlock case passReturnBy of
      PassBy.Value Representation.Empty -> "ret " <> llvmReturnType passReturnBy
      _ -> "ret " <> llvmReturnType passReturnBy <> " " <> operand result
    basicBlocks <- gets (.basicBlocks)
    pure
      ( functionName
      , "define "
          <> linkage
          <> "fastcc "
          <> llvmReturnType passReturnBy
          <> " "
          <> liftedName functionName
          <> parens
            [ llvmType passBy <> " " <> varName parameter
            | (passBy, parameter) <- toList parameters
            ]
          <> " align "
          <> Builder.intDec alignment
          <> " {"
          <> basicBlocks
          <> "\n}"
      )
  where
    fromLocal (Local l) = l
    fromLocal _ = panic "non-local function parameter"
    linkage =
      case functionName of
        Name.Lifted _ 0 ->
          ""
        _ ->
          "private "
    alignment :: (Num a) => a
    alignment = 8

assembleConstant
  :: Name.Lifted
  -> Representation
  -> Syntax.Term Void
  -> Assembler [(Name.Lifted, Builder)]
assembleConstant constantName repr term = do
  entry <- freshVar "entry"
  startBlock entry
  (_result, stack) <- assembleTerm Index.Seq.Empty Nothing (PassBy.Value mempty) term
  mapM_ restoreStack stack
  endBlock "ret void"
  basicBlocks <- gets (.basicBlocks)
  let init = initName constantName
  pure
    [
      ( init
      , "define "
          <> linkage
          <> "fastcc void "
          <> liftedName init
          <> "()"
          <> " align "
          <> Builder.intDec alignment
          <> " {"
          <> basicBlocks
          <> "\n}"
      )
    ,
      ( constantName
      , liftedName constantName
          <> " = global "
          <> llvmType (PassBy.Value repr)
          <> " zeroinitializer"
      )
    ]
  where
    linkage =
      case constantName of
        Name.Lifted _ 0 ->
          ""
        _ ->
          "private "
    alignment :: (Num a) => a
    alignment = 8

assembleTerm
  :: Environment v
  -> Maybe Name
  -> PassBy
  -> Syntax.Term v
  -> Assembler (Operand, Maybe Var)
assembleTerm env nameSuggestion passBy = \case
  Syntax.Operand o -> do
    (_, o') <- assembleOperand env o
    pure (o', Nothing)
  Syntax.Let passLetBy name term body -> do
    (termResult, termStack) <- assembleTerm env (Just name) passLetBy term
    (bodyResult, bodyStack) <- assembleTerm (env Index.Seq.:> (passLetBy, termResult)) nameSuggestion passBy body
    mapM_ restoreStack termStack
    mapM_ restoreStack bodyStack
    pure (bodyResult, Nothing)
  Syntax.Seq term1 term2 -> do
    (_, stack1) <- assembleTerm env Nothing (PassBy.Value Representation.Empty) term1
    (result, stack2) <- assembleTerm env nameSuggestion passBy term2
    mapM_ restoreStack stack1
    mapM_ restoreStack stack2
    pure (result, Nothing)
  Syntax.Case scrutinee branches defaultBranch -> do
    scrutinee' <- assembleOperand env scrutinee
    branchLabels <- forM branches \case
      Syntax.ConstructorBranch constr _ -> do
        label <- freshVar $ Name.Name $ show (pretty constr)
        (_, maybeTag) <- fetch $ Query.ConstructorRepresentation constr
        pure (fromMaybe (panic "case: no tag") maybeTag, label)
      Syntax.LiteralBranch (Literal.Integer i) _ -> do
        label <- freshVar $ Name.Name $ "integer_" <> show i
        pure (fromIntegral i, label)
    defaultLabel <- freshVar "default"
    afterSwitchLabel <- freshVar "after_switch"
    endBlock $
      "switch "
        <> typedOperand scrutinee'
        <> ", label "
        <> varName defaultLabel
        <> " "
        <> brackets
          [ separate
              " "
              [ typedOperand (PassBy.Value Representation.int, Constant $ Builder.intDec i)
                <> ", label "
                <> varName l
              | (i, l) <- branchLabels
              ]
          ]
    branchResults <- forM (zip branchLabels branches) \((_, branchLabel), branch) -> do
      startBlock branchLabel
      (result, stack) <- assembleTerm env nameSuggestion passBy $ Syntax.branchTerm branch
      mapM_ restoreStack stack
      endBlock $ "br label " <> varName afterSwitchLabel
      pure result
    startBlock defaultLabel
    maybeDefaultResult <- forM defaultBranch \branch -> do
      (result, stack) <- assembleTerm env nameSuggestion passBy branch
      mapM_ restoreStack stack
      pure result
    let defaultResult = fromMaybe (Constant "undef") maybeDefaultResult
    endBlock $ "br label " <> varName afterSwitchLabel
    startBlock afterSwitchLabel
    phiResult <- freshVar $ fromMaybe "switch_result" nameSuggestion
    emitInstruction $
      varName phiResult
        <> " = phi "
        <> llvmType passBy
        <> " "
        <> commaSeparate
          [ brackets [operand result, varName label]
          | (label, result) <- (defaultLabel, defaultResult) : zip (snd <$> branchLabels) branchResults
          ]
    pure (Local phiResult, Nothing)
  Syntax.Call name args -> do
    declareGlobal name
    args' <- mapM (assembleOperand env) args
    case passBy of
      PassBy.Value Representation.Empty -> do
        emitInstruction $
          "call fastcc "
            <> llvmReturnType passBy
            <> " "
            <> liftedName name
            <> parens (typedOperand <$> args')
        pure (Constant "undef", Nothing)
      _ -> do
        result <- freshVar $ fromMaybe "call_result" nameSuggestion
        emitInstruction $
          varName result
            <> " = call fastcc "
            <> llvmReturnType passBy
            <> " "
            <> liftedName name
            <> parens (typedOperand <$> args')
        pure (Local result, Nothing)
  Syntax.StackAllocate size -> do
    stack <- saveStack
    size' <- assembleOperand env size
    (pointers, nonPointerBytes) <- extractSizeParts size'
    pointerBytes <- freshVar "pointer_bytes"
    emitInstruction $
      varName pointerBytes
        <> " = mul i32 "
        <> varName pointers
        <> ", "
        <> Builder.intDec Representation.wordBytes
    bytes <- freshVar "alloca_bytes"
    emitInstruction $
      varName bytes <> " = add i32 " <> varName pointerBytes <> ", " <> varName nonPointerBytes
    allocaBytes <- freshVar "alloca_bytes"
    emitInstruction $ varName allocaBytes <> " = alloca i32 " <> varName bytes
    nonPointerPointer <- freshVar "non_pointer_pointer"
    emitInstruction $
      varName nonPointerPointer
        <> " = getelementptr ptr, i8 "
        <> varName allocaBytes
        <> ", i32 "
        <> varName nonPointerBytes
    result <- constructTuple (fromMaybe "alloca_result" nameSuggestion) "ptr" allocaBytes "ptr" nonPointerPointer
    pure (Local result, Just stack)
  Syntax.HeapAllocate constr size -> do
    declareLLVMGlobal "sixten_heap_allocate" "declare i64 @sixten_heap_allocate(i64, i64)"
    var <- freshVar $ fromMaybe "heap_allocation" nameSuggestion
    (_, maybeTag) <- fetch $ Query.ConstructorRepresentation constr
    size' <- assembleOperand env size
    emitInstruction $
      varName var
        <> " = call i64 @sixten_heap_allocate"
        <> parens
          [ "i64 " <> Builder.intDec (fromMaybe 0 maybeTag)
          , typedOperand size'
          ]
    pure (Local var, Nothing)
  Syntax.HeapPayload pointer -> do
    declareLLVMGlobal "sixten_heap_payload" "declare {ptr, ptr} @sixten_heap_payload(i64)"
    var <- freshVar $ fromMaybe "heap_payload" nameSuggestion
    pointer' <- assembleOperand env pointer
    emitInstruction $
      varName var
        <> " = call {ptr, ptr} @sixten_heap_payload"
        <> parens [typedOperand pointer']
    pure (Local var, Nothing)
  Syntax.PointerTag pointer -> do
    declareLLVMGlobal "sixten_heap_tag" "declare i64 @sixten_heap_tag(i64)"
    var <- freshVar $ fromMaybe "pointer_tag" nameSuggestion
    pointer' <- assembleOperand env pointer
    emitInstruction $
      varName var
        <> " = call i64 sixten_heap_tag"
        <> parens [typedOperand pointer']
    pure (Local var, Nothing)
  Syntax.Offset base size -> do
    base' <- assembleOperand env base
    size' <- assembleOperand env size
    (pointers, nonPointerBytes) <- extractSizeParts size'
    (pointerPointer, nonPointerPointer) <- extractParts base'
    updatedPointerPointer <- freshVar "updated_pointer_pointer"
    updatedNonPointerPointer <- freshVar "updated_non_pointer_pointer"
    emitInstruction $
      varName updatedPointerPointer
        <> " = getelementptr ptr, ptr "
        <> operand pointerPointer
        <> ", i32 "
        <> varName pointers
    emitInstruction $
      varName updatedNonPointerPointer
        <> " = getelementptr ptr, i8 "
        <> operand nonPointerPointer
        <> ", i32 "
        <> varName nonPointerBytes
    result <-
      constructTuple
        (fromMaybe "offset_pointers" nameSuggestion)
        "ptr"
        updatedPointerPointer
        "ptr"
        updatedNonPointerPointer
    pure (Local result, Nothing)
  Syntax.Copy dst src size -> do
    dst' <- assembleOperand env dst
    src' <- assembleOperand env src
    size' <- assembleOperand env size
    (pointers, nonPointerBytes) <- extractSizeParts size'
    (dstPointerPointer, dstNonPointerPointer) <- extractParts dst'
    (srcPointerPointer, srcNonPointerPointer) <- extractParts src'
    declareLLVMGlobal "llvm.memcpy.p0.p0.i32" "declare void @llvm.memcpy.p0.p0.i32(ptr, ptr, i32, i1)"
    pointerBytes <- freshVar "pointer_bytes"
    emitInstruction $
      varName pointerBytes
        <> " = mul i32 "
        <> varName pointers
        <> ", "
        <> Builder.intDec Representation.wordBytes
    emitInstruction $
      "call void @llvm.memcpy.p0.p0"
        <> parens
          [ "ptr " <> operand dstPointerPointer
          , "ptr " <> operand srcPointerPointer
          , "i32 " <> varName pointerBytes
          , "i1 0" -- isvolatile
          ]
    emitInstruction $
      "call void @llvm.memcpy.p0.p0"
        <> parens
          [ "ptr " <> operand dstNonPointerPointer
          , "ptr " <> operand srcNonPointerPointer
          , "i32 " <> varName nonPointerBytes
          , "i1 0" -- isvolatile
          ]
    pure (Constant "undef", Nothing)
  Syntax.Store dst src repr -> do
    dst' <- assembleOperand env dst
    src' <- assembleOperand env src
    (dstPointerPointer, dstNonPointerPointer) <- extractParts dst'
    case (pointerType repr.pointers, nonPointerType repr.nonPointerBytes) of
      (Nothing, Nothing) -> pure ()
      (Just _, Nothing) ->
        emitInstruction $ "store " <> typedOperand src' <> ", ptr " <> operand dstPointerPointer
      (Nothing, Just _) ->
        emitInstruction $ "store " <> typedOperand src' <> ", ptr " <> operand dstNonPointerPointer
      (Just p, Just np) -> do
        (pointerSrc, nonPointerSrc) <- extractParts src'
        emitInstruction $ "store " <> p <> " " <> operand pointerSrc <> ", ptr " <> operand dstPointerPointer
        emitInstruction $ "store " <> np <> " " <> operand nonPointerSrc <> ", ptr " <> operand dstNonPointerPointer
    pure (Constant "undef", Nothing)
  Syntax.Load src repr -> do
    src' <- assembleOperand env src
    (srcPointerPointer, srcNonPointerPointer) <- extractParts src'
    case (pointerType repr.pointers, nonPointerType repr.nonPointerBytes) of
      (Nothing, Nothing) -> pure (Constant "undef", Nothing)
      (Just p, Nothing) -> do
        result <- freshVar $ fromMaybe "load_result" nameSuggestion
        emitInstruction $ varName result <> " = load " <> p <> ", ptr " <> operand srcPointerPointer
        pure (Local result, Nothing)
      (Nothing, Just np) -> do
        result <- freshVar $ fromMaybe "load_result" nameSuggestion
        emitInstruction $ varName result <> " = load " <> np <> ", ptr " <> operand srcNonPointerPointer
        pure (Local result, Nothing)
      (Just p, Just np) -> do
        pointers <- freshVar "load_pointers"
        nonPointers <- freshVar "load_non_pointers"
        emitInstruction $ varName pointers <> " = load " <> p <> ", ptr " <> operand srcPointerPointer
        emitInstruction $ varName nonPointers <> " = load " <> np <> ", ptr " <> operand srcNonPointerPointer
        result <- constructTuple (fromMaybe "load_result" nameSuggestion) p pointers np nonPointers
        pure (Local result, Nothing)

assembleOperand :: Environment v -> Syntax.Operand v -> Assembler (PassBy, Operand)
assembleOperand env = \case
  Syntax.Var index -> pure $ Index.Seq.index env index
  Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Syntax.ConstantSignature repr ->
        pure
          ( PassBy.Reference
          , case (pointerType repr.pointers, nonPointerType repr.nonPointerBytes) of
              (Nothing, Nothing) -> ConstantReference "null" "null"
              (Just _, Nothing) -> ConstantReference (liftedName global) "null"
              (Nothing, Just _) -> ConstantReference "null" (liftedName global)
              (Just _, Just _) -> do
                let name = liftedName global
                ConstantReference
                  name
                  ( "getelementptr"
                      <> parens
                        [ llvmType $ PassBy.Value repr
                        , name
                        , Builder.intDec 0
                        , Builder.intDec 1
                        ]
                  )
          )
      _ -> panic "assembleOperand: global without constant signature"
  Syntax.Literal (Literal.Integer int) -> pure (PassBy.Value Representation.int, Constant $ Builder.integerDec int)
  Syntax.Representation repr ->
    pure
      ( PassBy.Value Representation.type_
      , Constant $
          Builder.word64Dec (fromIntegral repr.pointers .|. fromIntegral repr.nonPointerBytes `shiftL` 32)
      )
  Syntax.Tag constr -> do
    (_, maybeTag) <- fetch $ Query.ConstructorRepresentation constr
    pure (PassBy.Value Representation.int, Constant $ Builder.intDec $ fromMaybe 0 maybeTag)
  Syntax.Undefined repr -> pure (PassBy.Value repr, Constant "undef")

extractParts :: (PassBy, Operand) -> Assembler (Operand, Operand)
extractParts = \case
  (PassBy.Reference, ConstantReference a b) -> pure (Constant a, Constant b)
  reference -> do
    pointerPointer <- freshVar "pointer_pointer"
    nonPointerPointer <- freshVar "non_pointer_pointer"
    emitInstruction $
      varName pointerPointer
        <> " = extractvalue "
        <> typedOperand reference
        <> ", 0"
    emitInstruction $
      varName nonPointerPointer
        <> " = extractvalue "
        <> typedOperand reference
        <> ", 1"
    pure (Local pointerPointer, Local nonPointerPointer)

extractSizeParts :: (PassBy, Operand) -> Assembler (Var, Var)
extractSizeParts size@(passBy, _) = do
  pointers <- freshVar "pointers"
  nonPointerBytes <- freshVar "non_pointer_bytes"
  shifted <- freshVar "shifted"
  emitInstruction $
    varName pointers
      <> " = "
      <> "trunc "
      <> typedOperand size
      <> " to i32"
  emitInstruction $
    varName shifted
      <> " = "
      <> "lshr "
      <> typedOperand size
      <> ", 32"
  emitInstruction $
    varName nonPointerBytes
      <> " = "
      <> "trunc "
      <> typedOperand (passBy, Local shifted)
      <> " to "
      <> "i32"
  pure (pointers, nonPointerBytes)

constructTuple :: Name -> Builder -> Var -> Builder -> Var -> Assembler Var
constructTuple name type1 operand1 type2 operand2 = do
  struct <- freshVar "struct"
  emitInstruction $
    varName struct
      <> " = insertvalue "
      <> braces [type1, type2]
      <> " undef, "
      <> type1
      <> " "
      <> varName operand1
      <> ", 0"
  result <- freshVar name
  emitInstruction $
    varName result
      <> " = insertvalue "
      <> braces [type1, type2]
      <> " "
      <> varName struct
      <> ", "
      <> type2
      <> " "
      <> varName operand2
      <> ", 1"
  pure result
