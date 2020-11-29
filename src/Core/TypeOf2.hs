{-# language OverloadedStrings #-}
module Core.TypeOf2 where

import qualified Builtin
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import qualified Core.Domain as Domain
import qualified Core.Evaluation as Evaluation
import qualified Core.Syntax as Syntax
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Elaboration
import Elaboration.Context (Context)
import qualified Elaboration.Context as Context
import qualified Meta
import Monad
import Protolude hiding (typeOf)
import qualified Query
import Rock
import Telescope (Telescope)
import qualified Telescope

typeOf :: Context v -> Syntax.Term v -> M (Syntax.Term v)
typeOf context term = case term of
  Syntax.Var index ->
    Elaboration.readback context $ Context.lookupIndexType index context

  Syntax.Global global -> do
    type_ <- fetch $ Query.ElaboratedType global
    pure $ Syntax.fromVoid type_

  Syntax.Con constr -> do
    tele <- fetch $ Query.ConstructorType constr
    pure $ Syntax.fromVoid $ Telescope.fold Syntax.Pi tele

  Syntax.Lit lit ->
    Elaboration.readback context $ Elaboration.inferLiteral lit

  Syntax.Meta index -> do
    solution <- Context.lookupMeta index context
    pure $
      case solution of
        Meta.Unsolved type' _ ->
          type'

        Meta.Solved _ type' ->
          type'

  Syntax.Let bindings term' type_ body -> do
    value <- Elaboration.evaluate context term'
    type' <- Elaboration.evaluate context type_
    (context', _) <- Context.extendDef context (Bindings.toName bindings) value type'
    bodyType <- typeOf context' body
    pure $ Syntax.Let bindings term' type_ bodyType

  Syntax.Pi {} ->
    pure $ Syntax.Global Builtin.TypeName

  Syntax.Fun {} ->
    pure $ Syntax.Global Builtin.TypeName

  Syntax.Lam bindings domain plicity body -> do
    domain' <- Elaboration.evaluate context domain
    (context', _) <- Context.extend context (Bindings.toName bindings) domain'
    bodyType <- typeOf context' body
    pure $ Syntax.Pi (Binding.Unspanned $ Bindings.toName bindings) domain plicity bodyType

  Syntax.App function plicity argument -> do
    functionType <- valueTypeOf context function
    functionType' <- Context.forceHead context functionType
    case functionType' of
      Domain.Pi _ _ plicity' targetClosure
        | plicity == plicity' -> do
          argument' <- Elaboration.evaluate context argument
          typeValue <- Evaluation.evaluateClosure targetClosure argument'
          Elaboration.readback context typeValue

      Domain.Fun _domain plicity' target
        | plicity == plicity' ->
          Elaboration.readback context target

      _ -> panic "Core.typeOf application of non-function"

  Syntax.Case _scrutinee branches defaultBranch ->
    case defaultBranch of
      Just term' ->
        typeOf context term'

      Nothing ->
        case branches of
          Syntax.ConstructorBranches _ constructorBranches ->
            case OrderedHashMap.elems constructorBranches of
              (_, branchTele):_ -> do
                typeValue <- typeOfConstructorBranch context branchTele
                Elaboration.readback context typeValue

              [] ->
                panic "TODO type of branchless case"

          Syntax.LiteralBranches literalBranches ->
            case OrderedHashMap.elems literalBranches of
              (_, body):_ -> do
                typeOf context body

              [] ->
                panic "TODO type of branchless case"

  Syntax.Spanned _ term' ->
    typeOf context term'

valueTypeOf :: Context v -> Syntax.Term v -> M Domain.Value
valueTypeOf context term = case term of
  Syntax.Var index ->
    pure $ Context.lookupIndexType index context

  Syntax.Global {} ->
    viaTerm

  Syntax.Con {} ->
    viaTerm

  Syntax.Lit lit ->
    pure $ Elaboration.inferLiteral lit

  Syntax.Meta {} ->
    viaTerm

  Syntax.Let {} ->
    viaTerm

  Syntax.Pi {} ->
    pure Builtin.Type

  Syntax.Fun {} ->
    pure Builtin.Type

  Syntax.Lam {} ->
    viaTerm

  Syntax.App function plicity argument -> do
    functionType <- valueTypeOf context function
    functionType' <- Context.forceHead context functionType
    case functionType' of
      Domain.Pi _ _ plicity' targetClosure
        | plicity == plicity' -> do
          argument' <- Elaboration.evaluate context argument
          Evaluation.evaluateClosure targetClosure argument'

      Domain.Fun _domain plicity' target
        | plicity == plicity' ->
          pure target

      _ -> panic "Core.typeOf application of non-function"

  Syntax.Case _scrutinee branches defaultBranch ->
    case defaultBranch of
      Just term' ->
        valueTypeOf context term'

      Nothing ->
        case branches of
          Syntax.ConstructorBranches _ constructorBranches ->
            case OrderedHashMap.elems constructorBranches of
              (_, branchTele):_ ->
                typeOfConstructorBranch context branchTele

              [] ->
                panic "TODO type of branchless case"

          Syntax.LiteralBranches literalBranches ->
            case OrderedHashMap.elems literalBranches of
              (_, body):_ -> do
                valueTypeOf context body

              [] ->
                panic "TODO type of branchless case"

  Syntax.Spanned _ term' ->
    valueTypeOf context term'

  where
    viaTerm = do
      type_ <- typeOf context term
      Elaboration.evaluate context type_

typeOfConstructorBranch
  :: Context v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> M Domain.Value
typeOfConstructorBranch context tele =
  case tele of
    Telescope.Empty branch ->
      valueTypeOf context branch

    Telescope.Extend bindings type_ _ tele' -> do
      type' <- Elaboration.evaluate context type_
      (context', _) <- Context.extend context (Bindings.toName bindings) type'
      typeOfConstructorBranch context' tele'
