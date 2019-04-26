{-# language DeriveFunctor #-}
{-# language GADTs #-}
module Elaboration where

import Protolude hiding (check)

import qualified Bound.Scope.Simple as Bound
import qualified Bound.Var as Bound

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Evaluation
import Monad
import qualified PreSyntax
import qualified Syntax

data Inferred term
  = Inferred term !(M Domain.Type)
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
  Checked result <-
    tc context term $ Check typ

  pure result

infer
  :: Context v
  -> PreSyntax.Term
  -> M (Inferred (Syntax.Term v))
infer context term =
  tc context term Infer

inferred
  :: Expected e
  -> Syntax.Term v
  -> M Domain.Type
  -> M (e (Syntax.Term v))
inferred expected term typ =
  case expected of
    Infer ->
      pure $ Inferred term typ

    Check expectedType -> do
      typ' <- typ
      unify typ' expectedType
      pure $ Checked term

tc
  :: Functor e
  => Context v
  -> PreSyntax.Term
  -> Expected e
  -> M (e (Syntax.Term v))
tc context term expected =
  case term of
    PreSyntax.Var name ->
      case Context.lookupName name context of
        Nothing -> do
          type_ <- typeOfGlobal name
          inferred
            expected
            (Syntax.Global name)
            (eval context type_)

        Just v ->
          inferred
            expected
            (Syntax.Var v)
            (Context.lookupType v context)

    PreSyntax.Let name term' body -> do
      Inferred term'' typ <- infer context term'

      let
        context' =
          Context.extendValue context name (eval context term'') typ

      body' <- tc context' body expected
      pure $ Syntax.Let term'' . Bound.Scope <$> body'

    PreSyntax.Pi name source domain -> do
      source' <- check context source Builtin.type_

      let
        context' =
          Context.extend context name $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      inferred
        expected
        (Syntax.Pi source' $ Bound.Scope domain')
        (pure Builtin.type_)

    PreSyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      inferred
        expected
        (Syntax.Fun source' domain')
        (pure Builtin.type_)

    PreSyntax.Lam name body ->
      case expected of
        Infer -> undefined
        Check (Domain.Pi source domainClosure) -> do
          let
            context' =
              Context.extend context name source

          domain <-
            Evaluation.evalClosure
              domainClosure
              (eval context' $ Syntax.Var $ Bound.B ())
          body' <- check context' body domain
          pure $ Checked (Syntax.Lam (Bound.Scope body'))

        Check (Domain.Fun source domain) -> do
          let
            context' =
              Context.extend context name source

          domain' <- domain
          body' <- check context' body domain'
          pure $ Checked (Syntax.Lam (Bound.Scope body'))

    PreSyntax.App function argument -> do
      Inferred function' functionType <- infer context function
      functionType' <- functionType

      case functionType' of
        Domain.Pi argumentType domainClosure -> do
          argumentType' <- argumentType
          argument' <- check context argument argumentType'
          inferred
            expected
            (Syntax.App function' argument')
            (Evaluation.evalClosure domainClosure (eval context argument'))

        Domain.Fun source domain -> do
          source' <- source
          case expected of
            Check expectedType -> do
              unify expectedType functionType'
              argument' <- check context argument source'
              pure $ Checked (Syntax.App function' argument')

            Infer -> do
              argument' <- check context argument source'
              pure $ Inferred (Syntax.App function' argument') domain


eval
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
eval context =
  Evaluation.eval (Context.values context)

typeOfGlobal
  :: Text
  -> M (Syntax.Type v)
typeOfGlobal =
  undefined

unify :: Domain.Value -> Domain.Value -> M ()
unify =
  undefined
