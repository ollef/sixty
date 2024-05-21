{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lower where

import Boxity
import qualified Builtin
import qualified ClosureConverted.Context as CC
import qualified ClosureConverted.Domain as CC.Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Representation2 as CC.Representation
import qualified ClosureConverted.Syntax as CC.Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Sequence as Seq
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Index (Index)
import qualified Index
import qualified Index.Map
import qualified Index.Map as Index (Map)
import Literal (Literal)
import qualified Literal
import Low.PassBy (PassBy)
import qualified Low.PassBy as PassBy
import Low.Representation (Representation)
import qualified Low.Representation as Representation
import qualified Low.Syntax
import Monad
import Name (Name)
import qualified Name
import Protolude hiding (nonEmpty, repr)
import qualified Query
import Rock.Core
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

data Value
  = Operand !Operand
  | Let !PassBy !Name !Var !Value !Value
  | Seq !Value !Value
  | Case !Operand [Branch] (Maybe Value)
  | Call !Name.Lifted [Operand]
  | StackAllocate !Operand
  | HeapAllocate !Name.QualifiedConstructor !Operand
  | Dereference !Operand
  | PointerTag !Operand
  | Offset !Operand !Operand
  | Copy !Operand !Operand !Operand
  | Store !Operand !Operand !Representation
  | Load !Operand !Representation
  deriving (Show)

data Operand
  = Var !Var
  | Global !Name.Lifted
  | Literal !Literal
  | Representation !Representation
  | Tag !Name.QualifiedConstructor
  deriving (Show)

data Branch
  = ConstructorBranch !Name.QualifiedConstructor !Value
  | LiteralBranch !Literal !Value
  deriving (Show)

data OperandRepresentation
  = Value !Representation
  | Reference !Operand
  deriving (Show)

data OperandStorage = OperandStorage !Operand !OperandRepresentation
  deriving (Show)

data Collectible
  = CollectibleLet !PassBy !Name !Var !Value
  | CollectibleSeq !Value
  deriving (Show)

data Function = Function [(Name, Var)] !Value

type Collect = StateT (Tsil Collectible) M

let_ :: PassBy -> Name -> Value -> Collect Operand
let_ repr name value = do
  var <- lift freshVar
  modify (Tsil.:> CollectibleLet repr name var value)
  pure $ Var var

letReference :: Name -> Value -> Collect Operand
letReference = let_ PassBy.Reference

letValue :: Representation -> Name -> Value -> Collect Operand
letValue = let_ . PassBy.Value

seq_ :: Value -> Collect ()
seq_ value = modify (Tsil.:> CollectibleSeq value)

collect :: PassBy -> Name -> Collect Operand -> Collect Operand
collect repr name m = do
  result <- lift $ runCollect m
  case result of
    Operand operand -> pure operand
    _ -> let_ repr name result

collectReference :: Name -> Collect Operand -> Collect Operand
collectReference = collect PassBy.Reference

collectValue :: Representation -> Name -> Collect Operand -> Collect Operand
collectValue = collect . PassBy.Value

runCollect :: Collect Operand -> M Value
runCollect = genRunCollect Operand (\_ v -> v)

genRunCollect :: (a -> Value) -> (a -> Value -> b) -> Collect a -> M b
genRunCollect f g m = do
  (result, collectibles) <- runStateT m mempty
  pure $
    g result $
      foldr
        ( \case
            CollectibleLet repr n var value -> mkLet repr n var value
            CollectibleSeq value -> Seq value
        )
        (f result)
        collectibles
  where
    mkLet _repr _name var value (Operand (Var var')) | var == var' = value
    mkLet repr name var value body = Let repr name var value body

addRepresentation :: Operand -> Operand -> Value
addRepresentation x y =
  Call (Name.Lifted Builtin.AddRepresentationName 0) [x, y]

definition :: Name.Lifted -> CC.Syntax.Definition -> M (Maybe Low.Syntax.Definition)
definition name = \case
  CC.Syntax.TypeDeclaration _ -> pure Nothing
  CC.Syntax.ConstantDefinition term -> constantDefinition term
  CC.Syntax.FunctionDefinition tele -> functionDefinition tele
  CC.Syntax.DataDefinition _boxity constrDefs -> do
    let Name.Lifted qname n = name
    when (n /= 0) $ panic "data isn't first def"
    compiled <- CC.Representation.compileData Environment.empty qname constrDefs
    constantDefinition compiled
  CC.Syntax.ParameterisedDataDefinition _boxity constrDefs -> do
    let Name.Lifted qname n = name
    when (n /= 0) $ panic "data isn't first def"
    compiled <- CC.Representation.compileParameterisedData Environment.empty qname constrDefs
    functionDefinition compiled
  where
    constantDefinition term = do
      signature <- fetch $ Query.LowSignature name
      case signature of
        Low.Syntax.ConstantSignature _ -> do
          value <- runCollect $ storeTerm CC.empty mempty (Global name) term
          let term' = readback Index.Map.Empty value
          pure $ Just $ Low.Syntax.ConstantDefinition term'
        _ -> panic "Constant without constant signature"

    functionDefinition tele = do
      signature <- fetch $ Query.LowSignature name
      case signature of
        Low.Syntax.FunctionSignature passArgsBy passReturnBy -> do
          functionValue <-
            genRunCollect (\(_, _, result) -> Operand result) (\(params, returns, _) body -> Function (returns <> params) body) $
              lowerFunction CC.empty mempty passArgsBy passReturnBy tele
          let function = readbackFunction Index.Map.Empty functionValue
          pure $ Just $ Low.Syntax.FunctionDefinition function
        _ -> panic "Function without function signature"

lowerFunction
  :: CC.Context v
  -> Seq OperandStorage
  -> [PassBy]
  -> PassBy
  -> Telescope Name CC.Syntax.Type CC.Syntax.Term v
  -> Collect ([(Name, Var)], [(Name, Var)], Operand)
lowerFunction context indices passArgsBy passReturnBy tele = case (tele, passArgsBy) of
  (Telescope.Empty body, []) -> case passReturnBy of
    PassBy.Value repr -> do
      result <- generateTermWithoutType context indices body
      resultValue <- forceValue repr result
      pure ([], [], resultValue)
    PassBy.Reference -> do
      dst <- lift freshVar
      result <- storeTerm context indices (Var dst) body
      pure ([], [("return", dst)], result)
  (Telescope.Empty _, _) -> panic "Function signature mismatch"
  (Telescope.Extend name type_ _plicity tele', passArgBy : passArgsBy') -> do
    type' <- lift $ Evaluation.evaluate (CC.toEnvironment context) type_
    operandRepr <- case passArgBy of
      PassBy.Value repr -> pure $ Value repr
      PassBy.Reference -> do
        size <- generateTypeSize context indices type_
        pure $ Reference size
    (context', var) <- lift $ CC.extend context type'
    let indices' = indices Seq.:|> OperandStorage (Var var) operandRepr
    (params, returns, result) <- lowerFunction context' indices' passArgsBy' passReturnBy tele'
    pure ((name, var) : params, returns, result)
  (Telescope.Extend {}, _) -> panic "Function signature mismatch"

storeOperand
  :: Operand
  -> OperandStorage
  -> Collect Operand
storeOperand dst (OperandStorage src srcOperandRepr) =
  case srcOperandRepr of
    Value srcRepr -> do
      seq_ $ Store dst src srcRepr
      pure $ Representation srcRepr
    Reference srcRepr -> do
      seq_ $ Copy dst src srcRepr
      pure srcRepr

forceValue
  :: Representation
  -> OperandStorage
  -> Collect Operand
forceValue dstRepr (OperandStorage src srcOperandRepr) =
  case srcOperandRepr of
    Value srcRepr -> do
      when (dstRepr /= srcRepr) $ panic "repr mismatch"
      pure src
    Reference _srcReprValue ->
      letValue dstRepr "loaded" $ Load src dstRepr

forceReference :: OperandStorage -> Collect Operand
forceReference (OperandStorage src srcOperandRepr) =
  case srcOperandRepr of
    Reference _ ->
      pure src
    Value srcRepr -> do
      allocated <- letReference "allocated" $ StackAllocate $ Representation srcRepr
      seq_ $ Copy allocated src $ Representation srcRepr
      pure allocated

storeTerm
  :: CC.Context v
  -> Seq OperandStorage
  -> Operand
  -> CC.Syntax.Term v
  -> Collect Operand
storeTerm context indices dst = \case
  CC.Syntax.Var (Index.Index index) -> do
    let src = Seq.index indices $ Seq.length indices - index - 1
    storeOperand dst src
  CC.Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Low.Syntax.ConstantSignature repr -> do
        seq_ $ Copy dst (Global global) $ Representation repr
        pure $ Representation repr
      _ -> panic "Global without constant signature"
  CC.Syntax.Con con typeParams args -> do
    (boxity, maybeTag) <- fetch $ Query.ConstructorRepresentation con
    let tagArgs = case maybeTag of
          Nothing -> args
          Just tag -> CC.Syntax.Lit (Literal.Integer $ fromIntegral tag) : args
    case boxity of
      Unboxed -> do
        let go argOffset arg = do
              argDst <- letReference "constr_arg_dst" $ Offset dst argOffset
              argSize <- storeTerm context indices argDst arg
              letValue Representation.type_ "constr_arg_offset" $ addRepresentation argOffset argSize
        foldM go dst tagArgs
      Boxed -> do
        sizeTerm <- lift $ boxedConstructorSize (CC.toEnvironment context) con typeParams args
        size <- generateTypeSize context indices sizeTerm
        pointer <- letValue Representation.pointer "boxed_constr" $ HeapAllocate con size
        constrDst <- letReference "deref_constr" $ Dereference pointer
        let go argOffset arg = do
              argDst <- letValue Representation.type_ "constr_arg_dst" $ Offset constrDst argOffset
              argSize <- storeTerm context indices argDst arg
              letValue Representation.type_ "constr_arg_offset" $ addRepresentation argOffset argSize
        foldM_ go dst args
        storeOperand dst $ OperandStorage pointer $ Value Representation.pointer
  CC.Syntax.Lit lit@(Literal.Integer _) -> storeOperand dst $ OperandStorage (Literal lit) $ Value Representation.int
  CC.Syntax.Let _ term type_ body -> do
    typeValue <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    termOperand <- generateTerm context indices term typeValue
    (context', _) <- lift $ CC.extend context typeValue
    storeTerm context' (indices Seq.:|> termOperand) dst body
  CC.Syntax.Function _ ->
    storeOperand dst $
      OperandStorage (Representation Representation.rawFunctionPointer) $
        Value Representation.type_
  CC.Syntax.Apply function args -> do
    signature <- fetch $ Query.LowSignature function
    case signature of
      Low.Syntax.FunctionSignature passArgsBy passReturnBy ->
        storeCall context indices dst function args passArgsBy passReturnBy
      _ -> panic "Applying non-function"
  CC.Syntax.Pi {} ->
    storeOperand dst $
      OperandStorage (Representation Representation.pointer) $
        Value Representation.type_
  CC.Syntax.Closure _global _args -> panic "TODO closure"
  CC.Syntax.ApplyClosure _fun _args -> panic "TODO closure"
  CC.Syntax.Case scrutinee _type branches maybeDefault -> do
    scrutinee' <- generateTermWithoutType context indices scrutinee
    branches' <- CC.Representation.compileBranches branches
    case branches' of
      CC.Representation.TaggedConstructorBranches Unboxed constrBranches -> do
        scrutineeRef <- forceReference scrutinee'
        tag <- letValue Representation.int "tag" $ Load scrutineeRef Representation.int
        payload <- letReference "payload" $ Offset scrutineeRef $ Representation Representation.int
        constrBranches' <- forM constrBranches \(constr, constrBranch) ->
          map (ConstructorBranch constr) $
            lift $
              runCollect $
                storeBranch context indices dst payload constrBranch
        defaultBranch <-
          forM maybeDefault $
            lift . runCollect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case tag constrBranches' defaultBranch
      CC.Representation.TaggedConstructorBranches Boxed constrBranches -> do
        scrutineeValue <- forceValue Representation.pointer scrutinee'
        tag <- letValue Representation.int "tag" $ PointerTag scrutineeValue
        payload <- letReference "payload" $ Dereference scrutineeValue
        constrBranches' <- forM constrBranches \(constr, constrBranch) ->
          map (ConstructorBranch constr) $ lift $ runCollect do
            storeBranch context indices dst payload constrBranch
        defaultBranch <- forM maybeDefault $ lift . runCollect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case tag constrBranches' defaultBranch
      CC.Representation.UntaggedConstructorBranch Unboxed constrBranch -> do
        payload <- forceReference scrutinee'
        storeBranch context indices dst payload constrBranch
      CC.Representation.UntaggedConstructorBranch Boxed constrBranch -> do
        scrutineeValue <- forceValue Representation.pointer scrutinee'
        payload <- letReference "payload" $ Dereference scrutineeValue
        storeBranch context indices dst payload constrBranch
      CC.Representation.LiteralBranches litBranches -> do
        scrutineeValue <- forceValue Representation.int scrutinee'
        litBranches' <- forM (OrderedHashMap.toList litBranches) \(lit, litBranch) ->
          map (LiteralBranch lit) $
            lift $
              runCollect $
                storeTerm context indices dst litBranch
        defaultBranch <- forM maybeDefault $ lift . runCollect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case scrutineeValue litBranches' defaultBranch

generateTypeSize
  :: CC.Context v
  -> Seq OperandStorage
  -> CC.Syntax.Type v
  -> Collect Operand
generateTypeSize context indices type_ =
  collectValue Representation.type_ "size" $ do
    size <- generateTermWithType context indices type_ $ CC.Syntax.Global $ Name.Lifted Builtin.TypeName 0
    forceValue Representation.type_ size

generateTermWithType
  :: CC.Context v
  -> Seq OperandStorage
  -> CC.Syntax.Term v
  -> CC.Syntax.Type v
  -> Collect OperandStorage
generateTermWithType context indices term type_ = do
  typeValue <-
    lift $
      CC.Domain.Lazy <$> lazy do
        Evaluation.evaluate (CC.toEnvironment context) type_
  generateTerm context indices term typeValue

generateTermWithoutType
  :: CC.Context v
  -> Seq OperandStorage
  -> CC.Syntax.Term v
  -> Collect OperandStorage
generateTermWithoutType context indices term = do
  typeValue <-
    lift $
      CC.Domain.Lazy <$> lazy do
        value <- Evaluation.evaluate (CC.toEnvironment context) term
        TypeOf.typeOf context value
  generateTerm context indices term typeValue

generateTerm
  :: CC.Context v
  -> Seq OperandStorage
  -> CC.Syntax.Term v
  -> CC.Domain.Type
  -> Collect OperandStorage
generateTerm context indices term typeValue = case term of
  CC.Syntax.Var (Index.Index index) -> pure $ Seq.index indices $ Seq.length indices - index - 1
  CC.Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Low.Syntax.ConstantSignature repr ->
        pure $ OperandStorage (Global global) $ Reference $ Representation repr
      _ -> panic "Global without constant signature"
  CC.Syntax.Con con typeParams args -> do
    (boxity, maybeTag) <- fetch $ Query.ConstructorRepresentation con
    let tagArgs = case maybeTag of
          Nothing -> args
          Just tag -> CC.Syntax.Lit (Literal.Integer $ fromIntegral tag) : args
    case boxity of
      Unboxed -> do
        type_ <- lift $ Readback.readback (CC.toEnvironment context) typeValue
        size <- generateTypeSize context indices type_
        unboxedCon <- letReference "unboxed_constr" $ StackAllocate size

        let go argOffset arg = do
              argDst <- letReference "constr_arg_dst" $ Offset unboxedCon argOffset
              argSize <- storeTerm context indices argDst arg
              letValue Representation.type_ "constr_arg_offset" $ addRepresentation argOffset argSize
        _ <- collectValue Representation.type_ "constr_fields" $ foldM go (Representation mempty) tagArgs
        pure $ OperandStorage unboxedCon $ Reference size
      Boxed -> do
        sizeTerm <- lift $ boxedConstructorSize (CC.toEnvironment context) con typeParams args
        size <- generateTypeSize context indices sizeTerm
        pointer <- letValue Representation.pointer "boxed_constr" $ HeapAllocate con size
        constrDst <- letReference "deref_constr" $ Dereference pointer
        let go argOffset arg = do
              argDst <- letReference "constr_arg_dst" $ Offset constrDst argOffset
              argSize <- storeTerm context indices argDst arg
              letValue Representation.type_ "constr_arg_offset" $ addRepresentation argOffset argSize
        _ <- collectValue Representation.type_ "constr_fields" $ foldM go (Representation mempty) args
        pure $ OperandStorage pointer $ Value Representation.pointer
  CC.Syntax.Lit lit@(Literal.Integer _) -> pure $ OperandStorage (Literal lit) $ Value Representation.int
  CC.Syntax.Let _name _term type_ body -> do
    type' <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    termOperand <- generateTerm context indices term type'
    (context', _) <- lift $ CC.extend context type'
    generateTerm context' (indices Seq.:|> termOperand) body typeValue
  CC.Syntax.Function _tele ->
    pure $ OperandStorage (Representation Representation.rawFunctionPointer) $ Value Representation.type_
  CC.Syntax.Apply function args -> do
    signature <- fetch $ Query.LowSignature function
    case signature of
      Low.Syntax.FunctionSignature passArgsBy (PassBy.Value returnRepr) -> do
        when (length passArgsBy /= length args) $ panic "arg length mismatch"
        let nonEmpty (PassBy.Value Representation.Empty) = False
            nonEmpty _ = True
        callResult <- collectValue returnRepr "call_result" do
          callArgs <- forM (filter (nonEmpty . fst) $ zip passArgsBy args) \(passBy, arg) -> do
            operand <- generateTermWithoutType context indices arg
            case passBy of
              PassBy.Value repr ->
                forceValue repr operand
              PassBy.Reference ->
                forceReference operand
          letValue returnRepr "call_result" $ Call function callArgs
        pure $ OperandStorage callResult $ Value returnRepr
      Low.Syntax.FunctionSignature passArgsBy passReturnBy -> do
        type_ <- lift $ Readback.readback (CC.toEnvironment context) typeValue
        size <- generateTypeSize context indices type_
        callResult <- letReference "call_destination" $ StackAllocate size
        _ <- collectValue Representation.type_ "store_call" $ storeCall context indices callResult function args passArgsBy passReturnBy
        pure $ OperandStorage callResult $ Reference size
      _ -> panic "Applying non-function"
  CC.Syntax.Pi _name _domain _target ->
    pure $
      OperandStorage (Representation Representation.pointer) $
        Value Representation.type_
  CC.Syntax.Closure {} -> panic "TODO closure"
  CC.Syntax.ApplyClosure {} -> panic "TODO closure"
  CC.Syntax.Case _scrutinee type_ _branches _maybeDefault -> do
    size <- generateTypeSize context indices type_
    dst <- letReference "case_dst" $ StackAllocate size
    _ <- storeTerm context indices dst term
    pure $ OperandStorage dst $ Reference size

storeCall
  :: CC.Context v
  -> Seq OperandStorage
  -> Operand
  -> Name.Lifted
  -> [CC.Syntax.Term v]
  -> [PassBy]
  -> PassBy
  -> Collect Operand
storeCall context indices dst function args passArgsBy passReturnBy = do
  when (length passArgsBy /= length args) $ panic "arg length mismatch"
  let nonEmpty (PassBy.Value Representation.Empty) = False
      nonEmpty _ = True
  collectValue Representation.type_ "call_result" do
    callArgs <- forM (filter (nonEmpty . fst) $ zip passArgsBy args) \(passBy, arg) -> do
      operand <- generateTermWithoutType context indices arg
      case passBy of
        PassBy.Value repr ->
          forceValue repr operand
        PassBy.Reference ->
          forceReference operand
    case passReturnBy of
      PassBy.Value repr -> do
        callResult <- letValue repr "call_result" $ Call function callArgs
        storeOperand dst $ OperandStorage callResult $ Value repr
      PassBy.Reference ->
        letReference "call_result_size" $ Call function (dst : callArgs)

storeBranch
  :: CC.Context v
  -> Seq OperandStorage
  -> Operand
  -> Operand
  -> Telescope Name CC.Syntax.Type CC.Syntax.Term v
  -> Collect Operand
storeBranch context indices dst payload = \case
  Telescope.Empty term -> storeTerm context indices dst term
  Telescope.Extend _name type_ _plicity tele -> do
    size <- generateTypeSize context indices type_
    typeValue <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    (context', _) <- lift $ CC.extend context typeValue
    let indices' = indices Seq.:|> OperandStorage payload (Reference size)
    payload' <- letReference "offset_payload" $ Offset payload size
    storeBranch context' indices' dst payload' tele

boxedConstructorSize
  :: CC.Domain.Environment v
  -> Name.QualifiedConstructor
  -> [CC.Syntax.Term v]
  -> [CC.Syntax.Term v]
  -> M (CC.Syntax.Term v)
boxedConstructorSize env con params args = do
  tele <- fetch $ Query.ClosureConvertedConstructorType con
  params' <- mapM (Evaluation.evaluate env) params
  args' <- mapM (Evaluation.evaluate env) args
  maybeResult <- Evaluation.applyTelescope env (Telescope.fromVoid tele) params' \env' type_ -> do
    type' <- Evaluation.evaluate env' type_
    size <- CC.Representation.compileBoxedConstructorFields env' type' args'
    Evaluation.evaluate env' size
  case maybeResult of
    Nothing -> panic "boxedConstructorSize: Data params length mismatch"
    Just result -> Readback.readback env result

-------------------------------------------------------------------------------

readbackFunction :: Index.Map v Var -> Function -> Low.Syntax.Function v
readbackFunction outerEnv (Function params body) =
  go outerEnv params
  where
    go :: Index.Map v Var -> [(Name, Var)] -> Low.Syntax.Function v
    go env [] = Low.Syntax.Body $ readback env body
    go env ((name, var) : params') =
      Low.Syntax.Parameter name $ go (env Index.Map.:> var) params'

readback :: Index.Map v Var -> Value -> Low.Syntax.Term v
readback env = \case
  Operand operand -> Low.Syntax.Operand $ readbackOperand env operand
  Let passBy name var value value' ->
    Low.Syntax.Let
      passBy
      name
      (readback env value)
      (readback (env Index.Map.:> var) value')
  Seq value value' ->
    Low.Syntax.Seq (readback env value) (readback env value')
  Case scrutinee branches maybeDefaultBranch ->
    Low.Syntax.Case
      (readbackOperand env scrutinee)
      (readbackBranch env <$> branches)
      (readback env <$> maybeDefaultBranch)
  Call fun args -> Low.Syntax.Call fun $ readbackOperand env <$> args
  StackAllocate repr -> Low.Syntax.StackAllocate $ readbackOperand env repr
  HeapAllocate con repr -> Low.Syntax.HeapAllocate con $ readbackOperand env repr
  Dereference operand -> Low.Syntax.Dereference $ readbackOperand env operand
  PointerTag operand -> Low.Syntax.PointerTag $ readbackOperand env operand
  Offset offset operand ->
    Low.Syntax.Offset
      (readbackOperand env offset)
      (readbackOperand env operand)
  Copy dst src size ->
    Low.Syntax.Copy
      (readbackOperand env dst)
      (readbackOperand env src)
      (readbackOperand env size)
  Store dst value repr -> Low.Syntax.Store (readbackOperand env dst) (readbackOperand env value) repr
  Load src repr -> Low.Syntax.Load (readbackOperand env src) repr

readbackOperand :: Index.Map v Var -> Operand -> Low.Syntax.Operand v
readbackOperand env = \case
  Var var -> Low.Syntax.Var $ readbackVar env var
  Global global -> Low.Syntax.Global global
  Literal lit -> Low.Syntax.Literal lit
  Representation repr -> Low.Syntax.Representation repr
  Tag tag -> Low.Syntax.Tag tag

readbackVar :: Index.Map v Var -> Var -> Index v
readbackVar env var =
  fromMaybe (panic "Lower.readbackVar") $
    Index.Map.elemIndex var env

readbackBranch :: Index.Map v Var -> Branch -> Low.Syntax.Branch v
readbackBranch env = \case
  ConstructorBranch con value -> Low.Syntax.ConstructorBranch con $ readback env value
  LiteralBranch lit value -> Low.Syntax.LiteralBranch lit $ readback env value
