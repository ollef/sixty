{-# language DeriveFunctor #-}
{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}
module Elaboration where

import Protolude hiding (Seq, force, check, evaluate)

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Evaluation
import Monad
import qualified Name
import qualified Presyntax
import Readback (readback)
import qualified Syntax
import qualified Unification

data Inferred term
  = Inferred term !(Lazy Domain.Type)
  deriving Functor

newtype Checked term
  = Checked term
  deriving Functor

data Expected f where
  Infer :: Expected Inferred
  Check :: Domain.Type -> Expected Checked

check
  :: Context v
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context term typ = do
  Checked result <- elaborate context term $ Check typ
  pure result

infer
  :: Context v
  -> Presyntax.Term
  -> M (Inferred (Syntax.Term v))
infer context term =
  elaborate context term Infer

inferred
  :: Context v
  -> Expected e
  -> Syntax.Term v
  -> Lazy Domain.Type
  -> M (e (Syntax.Term v))
inferred context expected term typ =
  case expected of
    Infer ->
      pure $ Inferred term typ

    Check expectedType -> do
      typ' <- force typ
      Unification.unify context typ' expectedType
      pure $ Checked term

elaborate
  :: Functor e
  => Context v
  -> Presyntax.Term
  -> Expected e
  -> M (e (Syntax.Term v))
elaborate context term expected = trace ("elaborate " <> show term :: Text) $
  case term of
    Presyntax.Var name ->
      case Context.lookupNameIndex name context of
        Nothing -> do
          let
            -- TODO do name resolution
            qualifiedName = Name.Qualified (Name.Module mempty) name
          type_ <- typeOfGlobal qualifiedName
          type' <- lazy $ evaluate context type_
          inferred
            context
            expected
            (Syntax.Global qualifiedName)
            type'

        Just i ->
          inferred
            context
            expected
            (Syntax.Var i)
            (Context.lookupIndexType i context)

    Presyntax.Let name term' body -> do
      Inferred term'' typ <- infer context term'
      typ' <- force typ
      typ'' <- Readback.readback (Context.toReadbackEnvironment context) typ'

      term''' <- lazy $ evaluate context term''
      (context', _) <- Context.extendDef context name term''' $ Lazy $ pure typ'

      body' <- elaborate context' body expected
      pure $ Syntax.Let name term'' typ'' <$> body'

    Presyntax.Pi name source domain -> do
      source' <- check context source Builtin.type_

      (context', _) <- Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      inferred
        context
        expected
        (Syntax.Pi name source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      inferred
        context
        expected
        (Syntax.Fun source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Lam name body ->
      let
        inferIt = do
          source <- Context.newMetaType context
          source' <- readback (Context.toReadbackEnvironment context) source
          (context', _) <- Context.extend context name (Lazy $ pure source)
          Inferred body' domain <- infer context' body
          type_ <- lazy $ do
            domain' <- force domain
            domain'' <- readback (Context.toReadbackEnvironment context') domain'
            pure
              $ Domain.Pi name (Lazy $ pure source)
              $ Evaluation.makeClosure (Context.toEvaluationEnvironment context) domain''

          inferred
            context
            expected
            (Syntax.Lam name source' body')
            type_
      in
      case expected of
        Infer ->
          inferIt

        Check expectedType -> do
          expectedType' <- Context.forceHead context expectedType
          case expectedType' of
            Domain.Pi _ source domainClosure -> do
              source' <- force source
              source'' <- readback (Context.toReadbackEnvironment context) source'
              (context', var) <- Context.extend context name source

              domain <-
                Evaluation.evaluateClosure
                  domainClosure
                  (Lazy $ pure $ Domain.var var)
              body' <- check context' body domain
              pure $ Checked (Syntax.Lam name source'' body')

            Domain.Fun source domain -> do
              source' <- force source
              source'' <- Readback.readback (Context.toReadbackEnvironment context) source'
              (context', _) <- Context.extend context name source

              domain' <- force domain
              body' <- check context' body domain'
              pure $ Checked (Syntax.Lam name source'' body')

            _ ->
              inferIt

    Presyntax.App function argument -> do
      Inferred function' functionType <- infer context function
      functionType' <- force functionType
      functionType'' <- Context.forceHead context functionType'

      case functionType'' of
        Domain.Pi _ source domainClosure -> do
          source' <- force source
          argument' <- check context argument source'
          argument'' <- lazy $ evaluate context argument'
          domain <- lazy $ Evaluation.evaluateClosure domainClosure argument''
          inferred
            context
            expected
            (Syntax.App function' argument')
            domain

        Domain.Fun source domain -> do
          source' <- force source
          case expected of
            Check expectedType -> do
              domain' <- force domain
              Unification.unify context expectedType domain'
              argument' <- check context argument source'
              pure $ Checked (Syntax.App function' argument')

            Infer -> do
              argument' <- check context argument source'
              pure $ Inferred (Syntax.App function' argument') domain

        _ -> do
          source <- Context.newMetaType context
          domain <- Context.newMetaType context
          let
            lazySource = Lazy (pure source)
            lazyDomain = Lazy (pure domain)
            metaFunctionType = Domain.Fun lazySource (Lazy (pure domain))

          Unification.unify context functionType'' metaFunctionType
          case expected of
            Check expectedType -> do
              Unification.unify context expectedType domain
              argument' <- check context argument source
              pure $ Checked (Syntax.App function' argument')

            Infer -> do
              argument' <- check context argument source
              pure $ Inferred (Syntax.App function' argument') lazyDomain

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEvaluationEnvironment context)

typeOfGlobal
  :: Name.Qualified
  -> M (Syntax.Type v)
typeOfGlobal global =
  if global == "Builtin.Type" then
    return $ Syntax.Global "Builtin.Type"

  else
    undefined
