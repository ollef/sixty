{-# language DeriveFunctor #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
module Elaboration where

import Protolude hiding (force, check, evaluate)

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Evaluation
import Index
import Monad
import qualified PreSyntax
import qualified Syntax

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
  -> PreSyntax.Term
  -> Domain.Type
  -> M (Syntax.Term v)
check context term typ = do
  Checked result <- elaborate context term $ Check typ
  pure result

infer
  :: Context v
  -> PreSyntax.Term
  -> M (Inferred (Syntax.Term v))
infer context term =
  elaborate context term Infer

inferred
  :: Expected e
  -> Syntax.Term v
  -> Lazy Domain.Type
  -> M (e (Syntax.Term v))
inferred expected term typ =
  case expected of
    Infer ->
      pure $ Inferred term typ

    Check expectedType -> do
      typ' <- force typ
      unify typ' expectedType
      pure $ Checked term

elaborate
  :: Functor e
  => Context v
  -> PreSyntax.Term
  -> Expected e
  -> M (e (Syntax.Term v))
elaborate context term expected =
  case term of
    PreSyntax.Var name ->
      case Context.lookupName name context of
        Nothing -> do
          type_ <- typeOfGlobal name
          type' <- lazy $ evaluate context type_
          inferred
            expected
            (Syntax.Global name)
            type'

        Just v ->
          inferred
            expected
            (Syntax.Var v)
            (Context.lookupType v context)

    PreSyntax.Let name term' body -> do
      Inferred term'' typ <- infer context term'

      term''' <- lazy $ evaluate context term''
      let
        context' =
          Context.extendValue context name term''' typ

      body' <- elaborate context' body expected
      pure $ Syntax.Let term'' . Scope <$> body'

    PreSyntax.Pi name source domain -> do
      source' <- check context source Builtin.type_

      let
        (context', _) =
          Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      inferred
        expected
        (Syntax.Pi source' $ Scope domain')
        (Lazy $ pure Builtin.type_)

    PreSyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      inferred
        expected
        (Syntax.Fun source' domain')
        (Lazy $ pure Builtin.type_)

    PreSyntax.Lam name body ->
      case expected of
        Infer -> undefined
        Check (Domain.Pi source domainClosure) -> do
          let
            (context', var) =
              Context.extend context name source

          domain <-
            Evaluation.evaluateClosure
              domainClosure
              (Lazy $ pure $ Domain.var var)
          body' <- check context' body domain
          pure $ Checked (Syntax.Lam (Scope body'))

        Check (Domain.Fun source domain) -> do
          let
            (context', _) =
              Context.extend context name source

          domain' <- force domain
          body' <- check context' body domain'
          pure $ Checked (Syntax.Lam (Scope body'))

    PreSyntax.App function argument -> do
      Inferred function' functionType <- infer context function
      functionType' <- force functionType

      case functionType' of
        Domain.Pi argumentType domainClosure -> do
          argumentType' <- force argumentType
          argument' <- check context argument argumentType'
          argument'' <- lazy $ evaluate context argument'
          domain <- lazy $ Evaluation.evaluateClosure domainClosure argument''
          inferred
            expected
            (Syntax.App function' argument')
            domain

        Domain.Fun source domain -> do
          source' <- force source
          case expected of
            Check expectedType -> do
              unify expectedType functionType'
              argument' <- check context argument source'
              pure $ Checked (Syntax.App function' argument')

            Infer -> do
              argument' <- check context argument source'
              pure $ Inferred (Syntax.App function' argument') domain

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.values context)

typeOfGlobal
  :: Text
  -> M (Syntax.Type v)
typeOfGlobal global =
  if global == "Type" then
    return $ Syntax.Global "Type"
  else
    undefined

  undefined

unify :: Domain.Value -> Domain.Value -> M ()
unify =
  undefined
