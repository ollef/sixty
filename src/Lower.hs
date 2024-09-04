{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Lower where

import Boxity
import qualified Builtin
import qualified ClosureConverted.Context as CC
import qualified ClosureConverted.Domain as CC.Domain
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Representation as CC.Representation
import qualified ClosureConverted.Syntax as CC.Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Data.OrderedHashMap as OrderedHashMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import qualified Environment
import Index (Index)
import qualified Index.Map
import qualified Index.Map as Index (Map)
import qualified Index.Seq
import qualified Index.Seq as Index (Seq)
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
import Prettyprinter
import Protolude hiding (moduleName, nonEmpty, repr)
import qualified Query
import Rock.Core
import Telescope (Telescope)
import qualified Telescope
import Var (Var)

data Value
  = Operand !Operand
  | Let !PassBy !Name !Var !LetOperation !Value
  | Seq !SeqOperation !Value
  deriving (Show)

data LetOperation
  = Case !Operand [Branch] (Maybe Value)
  | Call !Name.Lowered [Operand]
  | StackAllocate !Operand
  | HeapAllocate !Name.QualifiedConstructor !Operand
  | HeapPayload !Operand
  | PointerTag !Operand
  | Offset !Operand !Operand
  | Load !Operand !Representation
  deriving (Show)

data SeqOperation
  = Store !Operand !Operand !Representation
  | Copy !Operand !Operand !Operand
  deriving (Show)

data Operand
  = Var !Var
  | Global !Representation !Name.Lowered
  | Literal !Literal
  | Representation !Representation
  | Tag !Name.QualifiedConstructor
  | Undefined !Representation
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
  = CollectibleLet !PassBy !Name !Var !LetOperation
  | CollectibleSeq !SeqOperation
  deriving (Show)

data Function = Function [(Name, PassBy, Var)] !PassBy !Value

type Collect = StateT (Tsil Collectible) M

let_ :: PassBy -> Name -> LetOperation -> Collect Operand
let_ repr name operation = do
  var <- lift freshVar
  modify (Tsil.:> CollectibleLet repr name var operation)
  pure $ Var var

letReference :: Name -> LetOperation -> Collect Operand
letReference = let_ PassBy.Reference

letValue :: Representation -> Name -> LetOperation -> Collect Operand
letValue = let_ . PassBy.Value

seq_ :: SeqOperation -> Collect ()
seq_ value = modify (Tsil.:> CollectibleSeq value)

collect :: Collect Operand -> M Value
collect = genRunCollect Operand (\_ v -> v)

genRunCollect :: (a -> Value) -> (a -> Value -> b) -> Collect a -> M b
genRunCollect f g m = do
  (result, collectibles) <- runStateT m mempty
  pure $
    g result $
      foldr
        ( \case
            CollectibleLet repr n var operation -> Let repr n var operation
            CollectibleSeq operation -> Seq operation
        )
        (f result)
        collectibles

letCall :: PassBy -> Name -> Name.Lifted -> [Operand] -> Collect Operand
letCall passBy name = \cases
  (Name.Lifted Builtin.AddRepresentationName 0) [Representation x, Representation y] -> pure $ Representation $ x <> y
  (Name.Lifted Builtin.AddRepresentationName 0) [Representation Representation.Empty, y] -> pure y
  (Name.Lifted Builtin.AddRepresentationName 0) [x, Representation Representation.Empty] -> pure x
  (Name.Lifted Builtin.MaxRepresentationName 0) [Representation x, Representation y] -> pure $ Representation $ Representation.leastUpperBound x y
  (Name.Lifted Builtin.MaxRepresentationName 0) [Representation Representation.Empty, y] -> pure y
  (Name.Lifted Builtin.MaxRepresentationName 0) [x, Representation Representation.Empty] -> pure x
  global operands -> let_ passBy name $ Call (Name.Lowered global Name.Original) operands

pattern Original :: Name.Qualified -> Name.Lowered
pattern Original qname = Name.Lowered (Name.Lifted qname 0) Name.Original

letLoad :: Name -> Operand -> Representation -> Collect Operand
letLoad name = \cases
  (Global _ (Original Builtin.EmptyRepresentationName)) _ -> pure $ Representation mempty
  (Global _ (Original Builtin.PointerRepresentationName)) _ -> pure $ Representation Representation.pointer
  (Global _ (Original Builtin.UnitName)) _ -> pure $ Representation mempty
  (Global _ (Original Builtin.IntName)) _ -> pure $ Representation Representation.int
  _ Representation.Empty -> pure $ Undefined Representation.Empty
  operand repr -> letValue repr name $ Load operand repr

mkStore :: Operand -> Operand -> Representation -> Maybe SeqOperation
mkStore dst src = \case
  Representation.Empty -> Nothing
  repr -> Just $ Store dst src repr

letAddRepresentation :: Name -> Operand -> Operand -> Collect Operand
letAddRepresentation name x y =
  letCall (PassBy.Value Representation.type_) name (Name.Lifted Builtin.AddRepresentationName 0) [x, y]

letOffset :: Name -> Operand -> Operand -> Collect Operand
letOffset name base = \case
  Representation Representation.Empty -> pure base
  offset -> letReference name $ Offset base offset

definition :: Name.Lifted -> CC.Syntax.Definition -> M [(Name.Lowered, Low.Syntax.Definition)]
definition name = \case
  CC.Syntax.TypeDeclaration _ -> pure []
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
        Low.Syntax.ConstantSignature repr -> do
          initValue <- collect do
            inited <- letValue Representation.int "inited" $ Load (Global Representation.int initedName) Representation.int
            initBranch <- lift $ collect do
              seq_ $ Store (Global Representation.int initedName) (Literal $ Literal.Integer 1) Representation.int
              _ <- storeTerm CC.empty Index.Seq.Empty (Global repr (Name.Lowered name Name.Original)) term
              pure $ Undefined Representation.Empty
            _ <- letValue Representation.Empty "case_result" $ Case inited [LiteralBranch (Literal.Integer 0) initBranch] $ Just $ Operand $ Undefined Representation.Empty
            pure $ Undefined Representation.Empty
          let init = readback Index.Map.Empty initValue
          pure
            [ (Name.Lowered name Name.Original, Low.Syntax.ConstantDefinition repr)
            , (initedName, Low.Syntax.ConstantDefinition Representation.int)
            , (constantInitName name, Low.Syntax.FunctionDefinition $ Low.Syntax.Body (PassBy.Value Representation.Empty) init)
            ]
        _ -> panic "Constant without constant signature"
      where
        initedName = constantInitedName name

    functionDefinition tele = do
      signature <- fetch $ Query.LowSignature name
      case signature of
        Low.Syntax.FunctionSignature passArgsBy passReturnBy -> do
          functionValue <-
            genRunCollect (\(_, _, _, result) -> Operand result) (\(params, returns, passReturnBy', _) body -> Function (returns <> params) passReturnBy' body) $
              lowerFunction CC.empty Index.Seq.Empty passArgsBy passReturnBy tele
          let function = readbackFunction Index.Map.Empty functionValue
          pure [(Name.Lowered name Name.Original, Low.Syntax.FunctionDefinition function)]
        _ -> panic "Function without function signature"

lowerFunction
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> [PassBy]
  -> PassBy
  -> Telescope Name CC.Syntax.Type CC.Syntax.Term v
  -> Collect ([(Name, PassBy, Var)], [(Name, PassBy, Var)], PassBy, Operand)
lowerFunction context indices passArgsBy passReturnBy tele = case (tele, passArgsBy) of
  (Telescope.Empty body, []) -> case passReturnBy of
    PassBy.Value repr -> do
      result <- generateTermWithoutType context indices body
      resultValue <- forceValue repr result
      pure ([], [], passReturnBy, resultValue)
    PassBy.Reference -> do
      dst <- lift freshVar
      result <- storeTerm context indices (Var dst) body
      pure ([], [("return", PassBy.Reference, dst)], PassBy.Value Representation.type_, result)
  (Telescope.Empty _, _) -> panic "Function signature mismatch"
  (Telescope.Extend name type_ _plicity tele', passArgBy : passArgsBy') -> do
    type' <- lift $ Evaluation.evaluate (CC.toEnvironment context) type_
    operandRepr <- case passArgBy of
      PassBy.Value repr -> pure $ Value repr
      PassBy.Reference -> do
        size <- generateTypeSize context indices type_
        pure $ Reference size
    (context', var) <- lift $ CC.extend context type'
    let indices' = indices Index.Seq.:> OperandStorage (Var var) operandRepr
    (params, returns, passReturnBy', result) <- lowerFunction context' indices' passArgsBy' passReturnBy tele'
    pure ((name, passArgBy, var) : params, returns, passReturnBy', result)
  (Telescope.Extend {}, _) -> panic "Function signature mismatch"

storeOperand
  :: Operand
  -> OperandStorage
  -> Collect Operand
storeOperand dst (OperandStorage src srcOperandRepr) =
  case srcOperandRepr of
    Value srcRepr -> do
      mapM_ seq_ $ mkStore dst src srcRepr
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
      letLoad "loaded" src dstRepr

forceReference :: Maybe Name -> OperandStorage -> Collect Operand
forceReference nameSuggestion (OperandStorage src srcOperandRepr) =
  case srcOperandRepr of
    Reference _ ->
      pure src
    Value srcRepr -> do
      allocated <- letReference (fromMaybe "allocated" nameSuggestion) $ StackAllocate $ Representation srcRepr
      seq_ $ Store allocated src srcRepr
      pure allocated

storeTerm
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> Operand
  -> CC.Syntax.Term v
  -> Collect Operand
storeTerm context indices dst = \case
  CC.Syntax.Var index -> do
    let src = Index.Seq.index indices index
    storeOperand dst src
  CC.Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Low.Syntax.ConstantSignature repr -> do
        seq_ $ Copy dst (Global repr $ Name.Lowered global Name.Original) $ Representation repr
        pure $ Representation repr
      _ -> panic "Global without constant signature"
  CC.Syntax.Con con typeParams args -> do
    (boxity, maybeTag) <- fetch $ Query.ConstructorRepresentation con
    let tagArgs = case maybeTag of
          Nothing -> args
          Just tag -> CC.Syntax.Lit (Literal.Integer $ fromIntegral tag) : args
    case boxity of
      Unboxed ->
        storeConstrArgs context indices (pure dst) (Representation mempty) tagArgs
      Boxed -> do
        sizeTerm <- lift $ boxedConstructorSize (CC.toEnvironment context) con typeParams args
        size <- generateTypeSize context indices sizeTerm
        pointer <- letValue Representation.pointer "boxed_constr" $ HeapAllocate con size
        let constrDst = letReference "payload" $ HeapPayload pointer
        storeConstrArgs_ context indices constrDst (pure $ Representation mempty) args
        storeOperand dst $ OperandStorage pointer $ Value Representation.pointer
  CC.Syntax.Lit lit@(Literal.Integer _) -> storeOperand dst $ OperandStorage (Literal lit) $ Value Representation.int
  CC.Syntax.Let name term type_ body -> do
    typeValue <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    termOperand <- generateTerm context (Just name) indices term typeValue
    (context', _) <- lift $ CC.extend context typeValue
    storeTerm context' (indices Index.Seq.:> termOperand) dst body
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
        scrutineeRef <- forceReference Nothing scrutinee'
        tag <- letLoad "tag" scrutineeRef Representation.int
        let payload name = letOffset name scrutineeRef $ Representation Representation.int
        constrBranches' <- forM constrBranches \(constr, constrBranch) ->
          map (ConstructorBranch constr) $
            lift $
              collect $
                storeBranch context indices dst payload constrBranch
        defaultBranch <-
          forM maybeDefault $
            lift . collect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case tag constrBranches' defaultBranch
      CC.Representation.TaggedConstructorBranches Boxed constrBranches -> do
        scrutineeValue <- forceValue Representation.pointer scrutinee'
        tag <- letValue Representation.int "tag" $ PointerTag scrutineeValue
        let payload name = letReference name $ HeapPayload scrutineeValue
        constrBranches' <- forM constrBranches \(constr, constrBranch) ->
          map (ConstructorBranch constr) $ lift $ collect do
            storeBranch context indices dst payload constrBranch
        defaultBranch <- forM maybeDefault $ lift . collect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case tag constrBranches' defaultBranch
      CC.Representation.UntaggedConstructorBranch Unboxed constrBranch -> do
        let payload name = forceReference (Just name) scrutinee'
        storeBranch context indices dst payload constrBranch
      CC.Representation.UntaggedConstructorBranch Boxed constrBranch -> do
        scrutineeValue <- forceValue Representation.pointer scrutinee'
        let payload name = letReference name $ HeapPayload scrutineeValue
        storeBranch context indices dst payload constrBranch
      CC.Representation.LiteralBranches litBranches -> do
        scrutineeValue <- forceValue Representation.int scrutinee'
        litBranches' <- forM (OrderedHashMap.toList litBranches) \(lit, litBranch) ->
          map (LiteralBranch lit) $
            lift $
              collect $
                storeTerm context indices dst litBranch
        defaultBranch <- forM maybeDefault $ lift . collect . storeTerm context indices dst
        letValue Representation.type_ "result" $ Case scrutineeValue litBranches' defaultBranch

storeConstrArgs
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> Collect Operand
  -> Operand
  -> [CC.Syntax.Term v]
  -> Collect Operand
storeConstrArgs context indices mdst offset = \case
  [] -> pure offset
  arg : args -> do
    dst <- mdst
    argDst <- letOffset "constr_arg_dst" dst offset
    argSize <- storeTerm context indices argDst arg
    offset' <- letAddRepresentation "constr_arg_offset" offset argSize
    storeConstrArgs context indices (pure dst) offset' args

storeConstrArgs_
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> Collect Operand
  -> Collect Operand
  -> [CC.Syntax.Term v]
  -> Collect ()
storeConstrArgs_ context indices mdst moffset = \case
  [] -> pure ()
  arg : args -> do
    dst <- mdst
    offset <- moffset
    argDst <- letOffset "constr_arg_dst" dst offset
    argSize <- storeTerm context indices argDst arg
    let offset' = letAddRepresentation "constr_arg_offset" offset argSize
    storeConstrArgs_ context indices (pure dst) offset' args

generateTypeSize
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> CC.Syntax.Type v
  -> Collect Operand
generateTypeSize context indices type_ = do
  size <- generateTermWithType context Nothing indices type_ $ CC.Syntax.Global $ Name.Lifted Builtin.TypeName 0
  forceValue Representation.type_ size

generateTermWithType
  :: CC.Context v
  -> Maybe Name
  -> Index.Seq v OperandStorage
  -> CC.Syntax.Term v
  -> CC.Syntax.Type v
  -> Collect OperandStorage
generateTermWithType context nameSuggestion indices term type_ = do
  typeValue <-
    lift $
      CC.Domain.Lazy <$> lazy do
        Evaluation.evaluate (CC.toEnvironment context) type_
  generateTerm context nameSuggestion indices term typeValue

generateTermWithoutType
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> CC.Syntax.Term v
  -> Collect OperandStorage
generateTermWithoutType context indices term = do
  typeValue <-
    lift $
      CC.Domain.Lazy <$> lazy do
        value <- Evaluation.evaluate (CC.toEnvironment context) term
        TypeOf.typeOf context value
  generateTerm context Nothing indices term typeValue

generateTerm
  :: CC.Context v
  -> Maybe Name
  -> Index.Seq v OperandStorage
  -> CC.Syntax.Term v
  -> CC.Domain.Type
  -> Collect OperandStorage
generateTerm context nameSuggestion indices term typeValue = case term of
  CC.Syntax.Var index -> pure $ Index.Seq.index indices index
  CC.Syntax.Global global -> do
    signature <- fetch $ Query.LowSignature global
    case signature of
      Low.Syntax.ConstantSignature repr ->
        pure $ OperandStorage (Global repr $ Name.Lowered global Name.Original) $ Reference $ Representation repr
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
        unboxedCon <- letReference (fromMaybe "unboxed_constr" nameSuggestion) $ StackAllocate size
        storeConstrArgs_ context indices (pure unboxedCon) (pure $ Representation mempty) tagArgs
        pure $ OperandStorage unboxedCon $ Reference size
      Boxed -> do
        sizeTerm <- lift $ boxedConstructorSize (CC.toEnvironment context) con typeParams args
        size <- generateTypeSize context indices sizeTerm
        pointer <- letValue Representation.pointer (fromMaybe "boxed_constr" nameSuggestion) $ HeapAllocate con size
        let constrPayload = letReference "constr_payload" $ HeapPayload pointer
        storeConstrArgs_ context indices constrPayload (pure $ Representation mempty) args
        pure $ OperandStorage pointer $ Value Representation.pointer
  CC.Syntax.Lit lit@(Literal.Integer _) -> pure $ OperandStorage (Literal lit) $ Value Representation.int
  CC.Syntax.Let name _term type_ body -> do
    type' <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    termOperand <- generateTerm context (Just name) indices term type'
    (context', _) <- lift $ CC.extend context type'
    generateTerm context' nameSuggestion (indices Index.Seq.:> termOperand) body typeValue
  CC.Syntax.Function _tele ->
    pure $ OperandStorage (Representation Representation.rawFunctionPointer) $ Value Representation.type_
  CC.Syntax.Apply function args -> do
    signature <- fetch $ Query.LowSignature function
    case signature of
      Low.Syntax.FunctionSignature passArgsBy passReturnBy@(PassBy.Value returnRepr) -> do
        when (length passArgsBy /= length args) $ panic "arg length mismatch"
        let nonEmpty (PassBy.Value Representation.Empty) = False
            nonEmpty _ = True
        callResult <- do
          callArgs <- forM (filter (nonEmpty . fst) $ zip passArgsBy args) \(passBy, arg) -> do
            operand <- generateTermWithoutType context indices arg
            case passBy of
              PassBy.Value repr ->
                forceValue repr operand
              PassBy.Reference ->
                forceReference Nothing operand
          letCall passReturnBy (fromMaybe "call_result" nameSuggestion) function callArgs
        pure $ OperandStorage callResult $ Value returnRepr
      Low.Syntax.FunctionSignature passArgsBy passReturnBy@PassBy.Reference -> do
        type_ <- lift $ Readback.readback (CC.toEnvironment context) typeValue
        size <- generateTypeSize context indices type_
        callResult <- letReference (fromMaybe "call_destination" nameSuggestion) $ StackAllocate size
        _ <- storeCall context indices callResult function args passArgsBy passReturnBy
        pure $ OperandStorage callResult $ Reference size
      _ -> panic "Applying non-function"
  CC.Syntax.Pi _name _domain _target ->
    pure $
      OperandStorage (Representation Representation.pointer) $
        Value Representation.type_
  CC.Syntax.Closure {} -> panic "TODO closure"
  CC.Syntax.ApplyClosure {} -> panic "TODO closure"
  CC.Syntax.Case scrutinee type_ branches maybeDefault -> do
    passTypeBy <- lift $ CC.Representation.passTypeBy (CC.toEnvironment context) typeValue
    case passTypeBy of
      PassBy.Reference -> do
        size <- generateTypeSize context indices type_
        dst <- letReference "case_dst" $ StackAllocate size
        _ <- storeTerm context indices dst term
        pure $ OperandStorage dst $ Reference size
      PassBy.Value repr -> do
        scrutinee' <- generateTermWithoutType context indices scrutinee
        branches' <- CC.Representation.compileBranches branches
        result <- case branches' of
          CC.Representation.TaggedConstructorBranches Unboxed constrBranches -> do
            scrutineeRef <- forceReference Nothing scrutinee'
            tag <- letLoad "tag" scrutineeRef Representation.int
            let payload name = letOffset name scrutineeRef $ Representation Representation.int
            constrBranches' <- forM constrBranches \(constr, constrBranch) ->
              map (ConstructorBranch constr) $
                lift $
                  collect $ 
                    generateBranch context indices payload repr typeValue constrBranch
            defaultBranch <-
              forM maybeDefault $ \branch ->
                lift $ collect $ do
                  branch' <- generateTerm context Nothing indices branch typeValue
                  forceValue repr branch'
            letValue repr "result" $ Case tag constrBranches' defaultBranch
          CC.Representation.TaggedConstructorBranches Boxed constrBranches -> do
            scrutineeValue <- forceValue Representation.pointer scrutinee'
            tag <- letValue Representation.int "tag" $ PointerTag scrutineeValue
            let payload name = letReference name $ HeapPayload scrutineeValue
            constrBranches' <- forM constrBranches \(constr, constrBranch) ->
              map (ConstructorBranch constr) $ lift $ collect do
                generateBranch context indices payload repr typeValue constrBranch
            defaultBranch <- forM maybeDefault $ \branch -> lift $ collect $ do
              branch' <- generateTerm context Nothing indices branch typeValue
              forceValue repr branch'
            letValue repr "result" $ Case tag constrBranches' defaultBranch
          CC.Representation.UntaggedConstructorBranch Unboxed constrBranch -> do
            let payload name = forceReference (Just name) scrutinee'
            generateBranch context indices payload repr typeValue constrBranch
          CC.Representation.UntaggedConstructorBranch Boxed constrBranch -> do
            scrutineeValue <- forceValue Representation.pointer scrutinee'
            let payload name = letReference name $ HeapPayload scrutineeValue
            generateBranch context indices payload repr typeValue constrBranch
          CC.Representation.LiteralBranches litBranches -> do
            scrutineeValue <- forceValue Representation.int scrutinee'
            litBranches' <- forM (OrderedHashMap.toList litBranches) \(lit, litBranch) ->
              map (LiteralBranch lit) $
                lift $
                  collect $ do
                    litBranch' <- generateTerm context Nothing indices litBranch typeValue
                    forceValue repr litBranch'
            defaultBranch <- forM maybeDefault $ \branch -> lift $ collect $ do
              branch' <- generateTerm context Nothing indices branch typeValue
              forceValue repr branch'
            letValue repr "result" $ Case scrutineeValue litBranches' defaultBranch
        pure $ OperandStorage result $ Value repr

storeCall
  :: CC.Context v
  -> Index.Seq v OperandStorage
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
  callArgs <- forM (filter (nonEmpty . fst) $ zip passArgsBy args) \(passBy, arg) -> do
    operand <- generateTermWithoutType context indices arg
    case passBy of
      PassBy.Value repr ->
        forceValue repr operand
      PassBy.Reference ->
        forceReference Nothing operand
  case passReturnBy of
    PassBy.Value repr -> do
      callResult <- letCall passReturnBy "call_result" function callArgs
      storeOperand dst $ OperandStorage callResult $ Value repr
    PassBy.Reference ->
      letCall (PassBy.Value Representation.type_) "call_result_size" function (dst : callArgs)

generateBranch
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> (Name -> Collect Operand)
  -> Representation
  -> CC.Domain.Type
  -> Telescope Name CC.Syntax.Type CC.Syntax.Term v
  -> Collect Operand
generateBranch context indices mpayload repr typeValue = \case
  Telescope.Empty term -> do
    term' <- generateTerm context Nothing indices term typeValue
    forceValue repr term'
  Telescope.Extend name type_ _plicity tele -> do
    payload <- mpayload name
    size <- generateTypeSize context indices type_
    fieldTypeValue <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    (context', _) <- lift $ CC.extend context fieldTypeValue
    let indices' = indices Index.Seq.:> OperandStorage payload (Reference size)
    let payload' name' = letOffset name' payload size
    generateBranch context' indices' payload' repr typeValue tele

storeBranch
  :: CC.Context v
  -> Index.Seq v OperandStorage
  -> Operand
  -> (Name -> Collect Operand)
  -> Telescope Name CC.Syntax.Type CC.Syntax.Term v
  -> Collect Operand
storeBranch context indices dst mpayload = \case
  Telescope.Empty term -> storeTerm context indices dst term
  Telescope.Extend name type_ _plicity tele -> do
    payload <- mpayload name
    size <- generateTypeSize context indices type_
    typeValue <- lift $ CC.Domain.Lazy <$> lazy (Evaluation.evaluate (CC.toEnvironment context) type_)
    (context', _) <- lift $ CC.extend context typeValue
    let indices' = indices Index.Seq.:> OperandStorage payload (Reference size)
    let payload' name' = letOffset name' payload size
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
  maybeResult <- Evaluation.applyTelescope env (Telescope.fromZero tele) params' \env' type_ -> do
    type' <- Evaluation.evaluate env' type_
    size <- CC.Representation.compileBoxedConstructorFields env' type' args'
    Evaluation.evaluate env' size
  case maybeResult of
    Nothing -> panic "boxedConstructorSize: Data params length mismatch"
    Just result -> Readback.readback env result

moduleInitName :: Name.Module -> Name.Lowered
moduleInitName moduleName =
  Name.Lowered (Name.Lifted (Name.Qualified moduleName "") 0) Name.Init

moduleInitedName :: Name.Module -> Name.Lowered
moduleInitedName moduleName =
  Name.Lowered (Name.Lifted (Name.Qualified moduleName "") 0) Name.Inited

constantInitName :: Name.Lifted -> Name.Lowered
constantInitName l =
  Name.Lowered l Name.Init

constantInitedName :: Name.Lifted -> Name.Lowered
constantInitedName l =
  Name.Lowered l Name.Inited

moduleInits :: [Name.Module] -> M Low.Syntax.Definition
moduleInits moduleNames = do
  value <- collect do
    forM_ moduleNames \moduleName ->
      letValue Representation.Empty "init-result" $ Call (moduleInitName moduleName) []
    pure $ Undefined Representation.Empty
  let term = readback Index.Map.Empty value
  pure $ Low.Syntax.FunctionDefinition $ Low.Syntax.Body (PassBy.Value Representation.Empty) term

moduleInit
  :: Name.Module
  -> [Name.Lowered]
  -> M [(Name.Lowered, Low.Syntax.Definition)]
moduleInit moduleName definitions = do
  initValue <- collect do
    inited <- letValue Representation.int "inited" $ Load (Global Representation.int initedName) Representation.int
    initBranch <- lift $ collect do
      seq_ $ Store (Global Representation.int initedName) (Literal $ Literal.Integer 1) Representation.int
      forM_ constantsToInitialize \defName ->
        letValue Representation.Empty "init-result" $ Call defName []
      pure $ Undefined Representation.Empty
    _ <- letValue Representation.Empty "case-result" $ Case inited [LiteralBranch (Literal.Integer 0) initBranch] $ Just $ Operand $ Undefined Representation.Empty
    pure $ Undefined Representation.Empty
  let init = readback Index.Map.Empty initValue
  pure
    [ (initedName, Low.Syntax.ConstantDefinition Representation.int)
    , (moduleInitName moduleName, Low.Syntax.FunctionDefinition $ Low.Syntax.Body (PassBy.Value Representation.Empty) init)
    ]
  where
    constantsToInitialize =
      [defName | defName@(Name.Lowered _ Name.Init) <- definitions]

    initedName = moduleInitedName moduleName

-------------------------------------------------------------------------------

readbackFunction :: Index.Map v Var -> Function -> Low.Syntax.Function v
readbackFunction outerEnv (Function params returnRepr body) =
  go outerEnv params
  where
    go :: Index.Map v Var -> [(Name, PassBy, Var)] -> Low.Syntax.Function v
    go env [] = Low.Syntax.Body returnRepr $ readback env body
    go env ((name, passParamBy, var) : params') =
      Low.Syntax.Parameter name passParamBy $ go (env Index.Map.:> var) params'

readback :: Index.Map v Var -> Value -> Low.Syntax.Term v
readback env = \case
  Operand operand -> Low.Syntax.Operand $ readbackOperand env operand
  Let passBy name var operation value' ->
    Low.Syntax.Let
      passBy
      name
      (readbackLetOperation env operation)
      (readback (env Index.Map.:> var) value')
  Seq operation value' ->
    Low.Syntax.Seq (readbackSeqOperation env operation) (readback env value')

readbackLetOperation :: Index.Map v Var -> LetOperation -> Low.Syntax.LetOperation v
readbackLetOperation env = \case
  Case scrutinee branches maybeDefaultBranch ->
    Low.Syntax.Case
      (readbackOperand env scrutinee)
      (readbackBranch env <$> branches)
      (readback env <$> maybeDefaultBranch)
  Call fun args -> Low.Syntax.Call fun $ readbackOperand env <$> args
  StackAllocate repr -> Low.Syntax.StackAllocate $ readbackOperand env repr
  HeapAllocate con repr -> Low.Syntax.HeapAllocate con $ readbackOperand env repr
  HeapPayload operand -> Low.Syntax.HeapPayload $ readbackOperand env operand
  PointerTag operand -> Low.Syntax.PointerTag $ readbackOperand env operand
  Offset base offset ->
    Low.Syntax.Offset
      (readbackOperand env base)
      (readbackOperand env offset)
  Load src repr -> Low.Syntax.Load (readbackOperand env src) repr

readbackSeqOperation :: Index.Map v Var -> SeqOperation -> Low.Syntax.SeqOperation v
readbackSeqOperation env = \case
  Copy dst src size ->
    Low.Syntax.Copy
      (readbackOperand env dst)
      (readbackOperand env src)
      (readbackOperand env size)
  Store dst value repr -> Low.Syntax.Store (readbackOperand env dst) (readbackOperand env value) repr

readbackOperand :: Index.Map v Var -> Operand -> Low.Syntax.Operand v
readbackOperand env = \case
  Var var -> Low.Syntax.Var $ readbackVar env var
  Global repr global -> Low.Syntax.Global repr global
  Literal lit -> Low.Syntax.Literal lit
  Representation repr -> Low.Syntax.Representation repr
  Tag tag -> Low.Syntax.Tag tag
  Undefined repr -> Low.Syntax.Undefined repr

readbackVar :: Index.Map v Var -> Var -> Index v
readbackVar env var =
  fromMaybe (panic "Lower.readbackVar") $
    Index.Map.elemIndex var env

readbackBranch :: Index.Map v Var -> Branch -> Low.Syntax.Branch v
readbackBranch env = \case
  ConstructorBranch con value -> Low.Syntax.ConstructorBranch con $ readback env value
  LiteralBranch lit value -> Low.Syntax.LiteralBranch lit $ readback env value
