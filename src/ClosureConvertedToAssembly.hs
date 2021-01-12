{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}

module ClosureConvertedToAssembly where

import Protolude hiding (IntMap, typeOf, local, moduleName)

import Rock

import qualified Assembly
import Boxity
import ClosureConverted.Context (Context)
import qualified ClosureConverted.Context as Context
import qualified ClosureConverted.Evaluation as Evaluation
import qualified ClosureConverted.Readback as Readback
import qualified ClosureConverted.Syntax as Syntax
import qualified ClosureConverted.TypeOf as TypeOf
import qualified Core.Syntax
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Tsil (Tsil)
import qualified Data.Tsil as Tsil
import Index
import qualified Literal
import Monad
import Name (Name(Name))
import qualified Name
import Query (Query)
import qualified Query
import Representation (Representation)
import qualified Representation
import qualified Scope
import Telescope (Telescope)
import qualified Telescope
import Var (Var(Var))

newtype Builder a = Builder (StateT BuilderState M a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadFetch Query, MonadState BuilderState)

data BuilderState = BuilderState
  { _fresh :: !Int
  , _instructions :: Tsil (Assembly.Instruction Assembly.BasicBlock)
  }

runBuilder :: Builder a -> M a
runBuilder (Builder s) =
  evalStateT s BuilderState
    { _fresh = 0
    , _instructions = mempty
    }

emit :: Assembly.Instruction Assembly.BasicBlock -> Builder ()
emit instruction =
  modify $ \s -> s { _instructions = _instructions s Tsil.:> instruction }

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
  Builder $ lift $ do
    type' <- Evaluation.evaluate (Context.toEnvironment $ _context env) type_
    (context', var) <- Context.extend (_context env) type'
    pure Environment
      { _context = context'
      , _varLocations = IntMap.insert var location $ _varLocations env
      }

data Return = Return
  { _returnLocation :: !Assembly.Operand
  , _returnType :: !Assembly.Operand
  }

operandNameSuggestion :: Assembly.Operand -> Assembly.NameSuggestion
operandNameSuggestion operand =
  case operand of
    Assembly.LocalOperand (Assembly.Local _ nameSuggestion) ->
      nameSuggestion

    Assembly.GlobalConstant global ->
      Assembly.NameSuggestion $ Assembly.nameText global

    Assembly.GlobalFunction global _ ->
      Assembly.NameSuggestion $ Assembly.nameText global

    Assembly.Lit _ ->
      "literal"

data Operand
  = Empty
  | Direct !Assembly.Operand -- ^ word sized
  | Indirect !Assembly.Operand

-------------------------------------------------------------------------------

indexLocation :: Index v -> Environment v -> Operand
indexLocation index env = do
  let
    var =
      Context.lookupIndexVar index $ _context env
  fromMaybe (panic "ClosureConvertedToAssembly.indexLocation") $
    IntMap.lookup var $ _varLocations env

globalConstantLocation :: Name.Lifted -> Operand
globalConstantLocation name =
  Indirect $ Assembly.GlobalConstant $ Assembly.Name name 0

stackAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
stackAllocate nameSuggestion size = do
  return_ <- freshLocal nameSuggestion
  emit $ Assembly.StackAllocate return_ size
  pure $ Assembly.LocalOperand return_

stackDeallocate :: Assembly.Operand -> Builder ()
stackDeallocate size =
  emit $ Assembly.StackDeallocate size

globalAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Assembly.Operand -> Builder Assembly.Operand
globalAllocate =
  add

heapAllocate :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
heapAllocate nameSuggestion size = do
  return_ <- freshLocal nameSuggestion
  emit $ Assembly.HeapAllocate return_ size
  pure $ Assembly.LocalOperand return_

typeOf :: Environment v -> Syntax.Term v -> Builder Assembly.Operand
typeOf env term = do
  type_ <- Builder $ lift $ do
    value <- Evaluation.evaluate (Context.toEnvironment $ _context env) term
    typeValue <- TypeOf.typeOf (_context env) value
    Readback.readback (Context.toEnvironment $ _context env) typeValue
  generateType env type_

sizeOfType :: Assembly.Operand -> Builder Assembly.Operand
sizeOfType =
  pure

-------------------------------------------------------------------------------

freshLocal :: Assembly.NameSuggestion -> Builder Assembly.Local
freshLocal nameSuggestion = do
  fresh <- gets _fresh
  modify $ \s -> s { _fresh = fresh + 1 }
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

call :: Name.Lifted -> [Assembly.Operand] -> Assembly.Operand -> Builder ()
call global args returnLocation =
  emit $ Assembly.CallVoid (Assembly.GlobalFunction (Assembly.Name global 0) $ 1 + length args) (returnLocation : args)

load :: Assembly.NameSuggestion -> Assembly.Operand -> Builder Assembly.Operand
load nameSuggestion pointer = do
  destination <- freshLocal nameSuggestion
  emit $ Assembly.Load destination pointer
  pure $ Assembly.LocalOperand destination

store :: Assembly.Operand -> Assembly.Operand -> Builder ()
store destination value =
  emit $ Assembly.Store destination value

initGlobal :: Name.Lifted -> Assembly.Operand -> Builder ()
initGlobal global value =
  emit $ Assembly.InitGlobal global value

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

-------------------------------------------------------------------------------

forceIndirect :: Operand -> Builder (Assembly.Operand, Builder ())
forceIndirect operand =
  case operand of
    Empty ->
      pure (Assembly.Lit $ Literal.Integer 0, pure ())

    Direct directOperand -> do
      operand' <- stackAllocate (operandNameSuggestion directOperand) pointerBytesOperand
      pure (operand', stackDeallocate pointerBytesOperand)

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

-------------------------------------------------------------------------------

moduleInitName :: Name.Module -> Name.Lifted
moduleInitName moduleName =
  Name.Lifted (Name.Qualified moduleName "$init") 0

initDefinitionName :: Name.Lifted -> Name.Lifted
initDefinitionName (Name.Lifted (Name.Qualified moduleName (Name.Name name)) m) =
  Name.Lifted (Name.Qualified moduleName $ Name.Name $ name <> "$init") m

generateModuleInit :: [(Name.Lifted, Syntax.Definition)] -> M (Assembly.Definition Assembly.BasicBlock, Int)
generateModuleInit definitions =
  runBuilder $ do
    globalPointer <- freshLocal "globals"
    outGlobalPointer <- freshLocal "globals_out"
    foldM_ (go $ Assembly.LocalOperand outGlobalPointer) (Assembly.LocalOperand globalPointer) definitions
    instructions <- gets _instructions
    fresh <- gets _fresh
    pure (Assembly.FunctionDefinition [outGlobalPointer, globalPointer] (Assembly.BasicBlock $ toList instructions), fresh)
  where
    go outGlobalPointer globalPointer (name, definition) =
      case definition of
        Syntax.TypeDeclaration _ ->
          pure globalPointer

        Syntax.ConstantDefinition {} -> do
          call (initDefinitionName name) [globalPointer] outGlobalPointer
          load "globals" outGlobalPointer

        Syntax.FunctionDefinition {} ->
          pure globalPointer

        Syntax.DataDefinition {} ->
          panic "gm dd" -- TODO

        Syntax.ParameterisedDataDefinition {} ->
          pure globalPointer

generateDefinition :: Name.Lifted -> Syntax.Definition -> M (Maybe (Assembly.Definition Assembly.BasicBlock, Int))
generateDefinition name@(Name.Lifted qualifiedName _) definition = do
  signature <- fetch $ Query.ClosureConvertedSignature name
  let
    env =
      emptyEnvironment $ Scope.KeyedName Scope.Definition qualifiedName
  runBuilder $
    case (definition, signature) of
      (Syntax.TypeDeclaration _, _) ->
        pure Nothing

      (Syntax.ConstantDefinition term, Just (Representation.ConstantSignature representation)) -> do
        globalPointer <- freshLocal "globals"
        outGlobalPointer <- freshLocal "globals_out"
        let
          globalPointerOperand =
            Assembly.LocalOperand globalPointer
          outGlobalPointerOperand =
            Assembly.LocalOperand outGlobalPointer
        type_ <- typeOf env term
        typeSize <- sizeOfType type_
        newGlobalPointer <- globalAllocate "globals" globalPointerOperand typeSize
        storeTerm env term Return
          { _returnLocation = globalPointerOperand
          , _returnType = type_
          }
        initGlobal name globalPointerOperand
        store outGlobalPointerOperand newGlobalPointer
        instructions <- gets _instructions
        fresh <- gets _fresh
        pure $ Just
          ( Assembly.ConstantDefinition [outGlobalPointer, globalPointer] $ Assembly.BasicBlock $ toList instructions
          , fresh
          )

      (Syntax.ConstantDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: ConstantDefinition without ConstantSignature"

      (Syntax.FunctionDefinition tele, Just (Representation.FunctionSignature parameterRepresentations returnRepresentation)) -> do
        returnLocation <- freshLocal "return_location"
        args <- generateFunction env returnLocation tele parameterRepresentations
        instructions <- gets _instructions
        fresh <- gets _fresh
        pure $ Just
          ( Assembly.FunctionDefinition (returnLocation : args) $ Assembly.BasicBlock $ toList instructions
          , fresh
          )

      (Syntax.FunctionDefinition {}, _) ->
        panic "ClosureConvertedToAssembly: ConstantDefinition without FunctionSignature"

      (Syntax.DataDefinition {}, _) ->
        panic "gd dd" -- TODO

      (Syntax.ParameterisedDataDefinition {}, _) ->
        panic "gd pd" -- TODO

generateFunction
  :: Environment v
  -> Assembly.Local
  -> Telescope Name Syntax.Type Syntax.Term v
  -> [Representation]
  -> Builder [Assembly.Local]
generateFunction env returnLocation tele parameterRepresentations =
  case (tele, parameterRepresentations) of
    (Telescope.Empty term, []) -> do
      type_ <- typeOf env term
      let
        return_ =
          Return
            { _returnLocation = Assembly.LocalOperand returnLocation
            , _returnType = type_
            }
      storeTerm env term return_
      pure []

    (Telescope.Extend (Name name) type_ _plicity tele', parameterRepresentation:parameterRepresentations') -> do
      (params, paramOperand) <-
        case parameterRepresentation of
          Representation.Empty ->
            pure ([], Empty)

          Representation.Direct -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure ([local], Direct $ Assembly.LocalOperand local)

          Representation.Indirect -> do
            local <- freshLocal $ Assembly.NameSuggestion name
            pure ([local], Indirect $ Assembly.LocalOperand local)

      env' <- extend env type_ paramOperand
      params' <- generateFunction env' returnLocation tele' parameterRepresentations'
      pure $ params <> params'

    _ ->
      panic "ClosureConvertedToAssembly.generateFunction: mismatched function telescope and signature"

-------------------------------------------------------------------------------

generateType :: Environment v -> Syntax.Type v -> Builder Assembly.Operand
generateType env type_ = do
  (type', deallocateType) <- generateTypedTerm env type_ pointerBytesOperand
  directType <- forceDirect type'
  deallocateType
  pure directType

generateTerm :: Environment v -> Syntax.Term v -> Builder (Return, Builder ())
generateTerm env term = do
  type_ <- typeOf env term
  (termOperand, deallocateTermOperand) <- generateTypedTerm env term type_
  (termLocation, deallocateTerm) <- forceIndirect termOperand
  let
    return_ =
      Return
        { _returnLocation = termLocation
        , _returnType = type_
        }
  pure (return_, deallocateTerm >> deallocateTermOperand)

generateTypedTerm :: Environment v -> Syntax.Term v -> Assembly.Operand -> Builder (Operand, Builder ())
generateTypedTerm env term type_ = do
  let
    stackAllocateIt = do
      typeSize <- sizeOfType type_
      termLocation <- stackAllocate "term_location" typeSize
      let
        return_ =
          Return
            { _returnLocation = termLocation
            , _returnType = type_
            }
      storeTerm env term return_
      pure (Indirect termLocation, stackDeallocate typeSize)

  case term of
    Syntax.Var index ->
      pure (indexLocation index env, pure ())

    Syntax.Global global ->
      pure (globalConstantLocation global, pure ())

    Syntax.Con {} ->
      stackAllocateIt

    Syntax.Lit {} ->
      stackAllocateIt

    Syntax.Let _name term' termType body -> do
      termType' <- generateType env termType
      (term'', deallocateTerm) <- generateTypedTerm env term' termType'
      env' <- extend env termType term''
      (result, deallocateBody) <- generateTypedTerm env' body type_
      deallocateTerm
      pure (result, deallocateBody >> deallocateTerm)

    Syntax.Function _ ->
      stackAllocateIt

    Syntax.Apply {} ->
      stackAllocateIt

    Syntax.Pi {} ->
      stackAllocateIt

    Syntax.Closure {} ->
      stackAllocateIt

    Syntax.ApplyClosure {} ->
      stackAllocateIt

    Syntax.Case {} ->
      stackAllocateIt

storeTerm
  :: Environment v
  -> Syntax.Term v
  -> Return
  -> Builder ()
storeTerm env term return_ =
  case term of
    Syntax.Var index -> do
      let
        varLocation =
          indexLocation index env
      returnTypeSize <- sizeOfType $ _returnType return_
      copy (_returnLocation return_) varLocation returnTypeSize

    Syntax.Global global -> do
      let
        location =
          globalConstantLocation global
      returnTypeSize <- sizeOfType $ _returnType return_
      copy (_returnLocation return_) location returnTypeSize

    Syntax.Con con@(Name.QualifiedConstructor typeName _) params args -> do
      maybeTag <- fetch $ Query.ConstructorTag con
      let
        tagArgs =
          case maybeTag of
            Nothing ->
              args

            Just tag ->
              Syntax.Lit (Literal.Integer $ fromIntegral tag) : args

        go location arg = do
          argType <- typeOf env arg
          storeTerm env arg Return
            { _returnType = argType
            , _returnLocation = location
            }
          argTypeSize <- sizeOfType argType
          add "argument_offset" location argTypeSize

      boxity <- fetchBoxity typeName
      case boxity of
        Unboxed ->
          foldM_ go (_returnLocation return_) tagArgs

        Boxed -> do
          size <- boxedConstructorSize env con params
          heapLocation <- heapAllocate "constructor_heap_object" size
          foldM_ go heapLocation tagArgs
          store (_returnLocation return_) heapLocation

    Syntax.Lit lit ->
      store (_returnLocation return_) (Assembly.Lit lit)

    Syntax.Let _name term' type_ body -> do
      type' <- generateType env type_
      (term'', deallocateTerm) <- generateTypedTerm env term' type'
      env' <- extend env type_ term''
      storeTerm env' body return_
      deallocateTerm

    Syntax.Function _ ->
      store (_returnLocation return_) pointerBytesOperand

    Syntax.Apply global arguments -> do
      maybeSignature <- fetch $ Query.ClosureConvertedSignature global
      let
        argumentRepresentations =
          case maybeSignature of
            Just (Representation.FunctionSignature argumentRepresentations_ returnRepresentation) ->
              argumentRepresentations_

            _ ->
              panic $ "ClosureConvertedToAssembly: Applying signature-less function " <> show global
      (arguments', deallocators) <- unzip <$> forM arguments (generateTerm env)
      args'' <- forM (zip argumentRepresentations arguments') $ \(representation, argument) ->
        case representation of
          Representation.Empty ->
            pure []

          Representation.Direct ->
            pure <$> forceDirect (Indirect $ _returnLocation argument)

          Representation.Indirect ->
            pure [_returnLocation argument]

      call global (concat args'') $ _returnLocation return_
      sequence_ $ reverse deallocators

    Syntax.Pi {} ->
      store (_returnLocation return_) pointerBytesOperand

    Syntax.Closure {} ->
      panic "st c" -- TODO

    Syntax.ApplyClosure {} ->
      panic "st ac" -- TODO

    Syntax.Case {} ->
      panic "st case" -- TODO

-------------------------------------------------------------------------------

fetchBoxity :: MonadFetch Query m => Name.Qualified -> m Boxity
fetchBoxity name = do
  maybeDef <- fetch $ Query.ElaboratedDefinition name
  case maybeDef of
    Just (Core.Syntax.DataDefinition boxity _, _) ->
      pure boxity

    _ ->
      panic "ClosureConvertedToAssembly.fetchBoxity"

boxedConstructorSize
  :: Environment v
  -> Name.QualifiedConstructor
  -> [Syntax.Term v]
  -> m Assembly.Operand
boxedConstructorSize =
  panic "bcs"
