{-# LANGUAGE GADTs #-}
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

data Expected term result where
  Infer :: Expected term (term, Domain.Type)
  Check :: Domain.Type -> Expected term term

mapResult :: Expected term result -> (term -> term) -> result -> result
mapResult expected f result =
  case expected of
    Infer -> first f result
    Check _ -> f result

check
  :: Context v
  -> PreSyntax.Term
  -> Domain.Type
  -> Syntax.Term v
check context term typ =
  tc context term $ Check typ

infer
  :: Context v
  -> PreSyntax.Term
  -> (Syntax.Term v, Domain.Type)
infer context term =
  tc context term Infer

instantiateExpected
  :: Expected (Syntax.Term v) result
  -> Syntax.Term v
  -> Domain.Type
  -> result
instantiateExpected expected term typ =
  case expected of
    Infer ->
      (term, typ)

    Check expectedType ->

      -- unify typ expectedType -- TODO
      term

tc
  :: Context v
  -> PreSyntax.Term
  -> Expected (Syntax.Term v) result
  -> result
tc context term expected =
  case term of
    PreSyntax.Var name ->
      case Context.lookupName name context of
        Nothing ->
          tcGlobal name expected

        Just (v, Context.Binding _ _ t) ->
          instantiateExpected expected (Syntax.Var v) t

    PreSyntax.Let name term body ->
      let
        (term', typ) =
          infer context term

        context' =
          Context.extendValue context name (eval context term') typ
      in
      case expected of
        Infer ->
          first (Syntax.Let term' . Bound.Scope) $ infer context' body

        Check typ ->
          Syntax.Let term' $ Bound.Scope $ check context' body typ

    PreSyntax.Pi name source domain ->
      let
        source' =
          check context source Builtin.type_

        context' =
          Context.extend context name Builtin.type_

        domain' =
          check context' domain Builtin.type_
      in
      instantiateExpected
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
eval = undefined

tcGlobal
  :: Text
  -> Expected (Syntax.Term v) result
  -> result
tcGlobal = undefined
