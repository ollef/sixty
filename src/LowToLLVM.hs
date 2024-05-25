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

data Operand
  = Local !Var
  | Global !Name.Lifted
  | Constant !Builder
  deriving (Show)

operand :: Operand -> Builder
operand = \case
  Local v -> varName v
  Global n -> liftedName n
  Constant c -> c

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
  PassBy.Reference -> "{ ptr, ptr }"
  PassBy.Value repr ->
    case (pointers repr.pointers, nonPointerBytes repr.nonPointerBytes) of
      (Nothing, Nothing) -> "{ }"
      (Just p, Nothing) -> p
      (Nothing, Just np) -> np
      (Just p, Just np) -> braces [p, np]
    where
      pointers = \case
        0 -> Nothing
        1 -> Just wordSizedInt
        n -> Just $ "[" <> Builder.word32Dec n <> " x " <> wordSizedInt <> "]"
      nonPointerBytes = \case
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
  declareLLVMGlobal "llvm.stackrestore" "declare ccc void @llvm.stackrestore(ptr)"
  var <- freshVar "stack"
  emitInstruction $ varName var <> " = call ccc ptr @llvm.stacksave()"
  pure var

restoreStack :: Var -> Assembler ()
restoreStack var = do
  declareLLVMGlobal "llvm.stacksave" "declare ccc ptr @llvm.stackesave()"
  emitInstruction $ "call ccc void @llvm.stackrestore" <> parens ["ptr " <> varName var]

-------------------------------------------------------------------------------

assembleModule :: [(Name.Lifted, Syntax.Definition)] -> M Lazy.ByteString
assembleModule definitions = do
  (assembledDefinitions, allUsedGlobals) <-
    unzip <$> forM definitions (runAssembler . uncurry assembleDefinition)
  let (usedGlobals, usedLLVMGlobals) = bimap mconcat mconcat $ unzip allUsedGlobals
      assembledDefinitions' = concat assembledDefinitions
  pure $
    Builder.toLazyByteString $
      separate "\n\n" $
        HashMap.elems usedLLVMGlobals <> map snd assembledDefinitions'

type Environment v = Index.Seq v (PassBy, Operand)

assembleDefinition :: Name.Lifted -> Syntax.Definition -> Assembler [(Name.Lifted, Builder)]
assembleDefinition name definition =
  case definition of
    Syntax.FunctionDefinition function ->
      pure <$> assembleFunction name Index.Seq.Empty function
    Syntax.ConstantDefinition _ _ -> undefined

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
    (result, stack) <- assembleTerm env Nothing passReturnBy term
    mapM_ restoreStack stack
    emitInstruction $ "ret " <> llvmType passReturnBy <> " " <> operand result
    basicBlocks <- gets (.basicBlocks)
    pure
      ( functionName
      , "define "
          <> linkage
          <> "fastcc "
          <> llvmType passReturnBy
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

assembleTerm :: Environment v -> Maybe Name -> PassBy -> Syntax.Term v -> Assembler (Operand, Maybe Var)
assembleTerm env nameSuggestion passBy = \case
  Syntax.Operand o -> do
    (_, o') <- assembleOperand env o
    pure (o', Nothing)
  Syntax.Let passBy' name term body -> do
    (termResult, termStack) <- assembleTerm env (Just name) passBy' term
    (bodyResult, bodyStack) <- assembleTerm (env Index.Seq.:> (passBy, termResult)) nameSuggestion passBy body
    mapM_ restoreStack termStack
    mapM_ restoreStack bodyStack
    pure (bodyResult, Nothing)
  Syntax.Seq term1 term2 -> do
    (_, stack1) <- assembleTerm env Nothing (PassBy.Value Representation.Empty) term1
    (result, stack2) <- assembleTerm env nameSuggestion passBy term2
    mapM_ restoreStack stack1
    mapM_ restoreStack stack2
    pure (result, Nothing)
  Syntax.Case scrutinee branches maybeDefault -> do
    scrutinee' <- assembleOperand env scrutinee
    branchLabels <- forM branches \case
      Syntax.ConstructorBranch constr _ -> do
        label <- freshVar $ Name.Name $ "branch_" <> show (pretty constr)
        (_, maybeTag) <- fetch $ Query.ConstructorRepresentation constr
        pure (fromMaybe (panic "case: no tag") maybeTag, label)
      Syntax.LiteralBranch (Literal.Integer i) _ -> do
        label <- freshVar $ Name.Name $ "branch_" <> show i
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
    _
  Syntax.Call name args -> do
    declareGlobal name
    var <- freshVar $ fromMaybe "call_result" nameSuggestion
    args' <- mapM (assembleOperand env) args
    emitInstruction $ varName var <> " = call fastcc " <> liftedName name <> " " <> parens (typedOperand <$> args')
    pure (Local var, Nothing)
  Syntax.StackAllocate size -> do
    stack <- saveStack
    size' <- assembleOperand env size
    var <- freshVar $ fromMaybe "alloca_result" nameSuggestion
    emitInstruction $ varName var <> " = alloca " <> typedOperand size'
    pure (Local var, Just stack)
  Syntax.HeapAllocate con size -> _
  Syntax.HeapPayload pointer -> _
  Syntax.PointerTag pointer -> _
  Syntax.Offset base size -> _
  Syntax.Copy dst src size -> _
  Syntax.Store dst src repr -> _
  Syntax.Load src repr -> _

assembleOperand :: Environment v -> Syntax.Operand v -> Assembler (PassBy, Operand)
assembleOperand env = \case
  Syntax.Var index -> pure $ Index.Seq.index env index
  Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Syntax.ConstantSignature repr -> pure (PassBy.Value repr, Global global)
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
