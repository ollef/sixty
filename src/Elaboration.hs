{-# language DeriveFunctor #-}
{-# language GADTs #-}
module Elaboration where

import Protolude hiding (check)

import qualified Bound.Scope.Simple as Bound

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Evaluation
import qualified PreSyntax
import qualified Syntax

data Inferred term
  = Inferred term Domain.Type
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
  -> Syntax.Term v
check context term typ =
  let
    Checked result =
      tc context term $ Check typ
  in
  result

infer
  :: Context v
  -> PreSyntax.Term
  -> Inferred (Syntax.Term v)
infer context term =
  tc context term Infer

inferred
  :: Expected e
  -> Syntax.Term v
  -> Domain.Type
  -> e (Syntax.Term v)
inferred expected term typ =
  case expected of
    Infer ->
      Inferred term typ

    Check expectedType ->

      -- unify typ expectedType -- TODO
      Checked term

tc
  :: Functor e
  => Context v
  -> PreSyntax.Term
  -> Expected e
  -> e (Syntax.Term v)
tc context term expected =
  case term of
    PreSyntax.Var name ->
      case Context.lookupName name context of
        Nothing ->
          inferred
            expected
            (Syntax.Global name)
            (eval context (typeOfGlobal name))

        Just v ->
          inferred expected (Syntax.Var v) (Context.lookupType v context)

    PreSyntax.Let name term body ->
      let
        Inferred term' typ =
          infer context term

        context' =
          Context.extendValue context name (eval context term') typ
      in
      Syntax.Let term' . Bound.Scope <$> tc context' body expected

    PreSyntax.Pi name source domain ->
      let
        source' =
          check context source Builtin.type_

        context' =
          Context.extend context name Builtin.type_

        domain' =
          check context' domain Builtin.type_
      in
      inferred
        expected
        (Syntax.Pi source' $ Bound.Scope domain')
        Builtin.type_

    PreSyntax.Lam name body ->
      undefined

    PreSyntax.App function argument ->
      undefined

eval
  :: Context v
  -> Syntax.Term v
  -> Domain.Value
eval context =
  Evaluation.eval (Context.values context)

typeOfGlobal
  :: Text
  -> Syntax.Type v
typeOfGlobal = undefined
