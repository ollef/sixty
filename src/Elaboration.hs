{-# language DeriveFunctor #-}
{-# language DuplicateRecordFields #-}
{-# language GADTs #-}
{-# language ScopedTypeVariables #-}
module Elaboration where

import Protolude hiding (Seq, force, check, evaluate)

import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import Rock

import qualified Builtin
import Context (Context)
import qualified Context
import qualified Domain
import qualified Error
import qualified Evaluation
import qualified Meta
import Monad
import qualified Name
import qualified Presyntax
import qualified Query
import qualified Readback
import qualified Resolution
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

inferTopLevel
  :: Resolution.KeyedName
  -> Presyntax.Term
  -> M (Syntax.Term Void, Syntax.Type Void, Syntax.MetaSolutions)
inferTopLevel key term = do
  context <- Context.empty key
  Inferred def' typeValue <- Elaboration.infer context term
  typeValue' <- force typeValue
  type_ <- readback context typeValue'
  metaSolutions <- checkMetaSolutions context
  let
    def'' = globaliseMetas (Resolution.unkeyed key) def'
    type' = globaliseMetas (Resolution.unkeyed key) type_
  pure (def'', type', metaSolutions)

checkTopLevel
  :: Resolution.KeyedName
  -> Presyntax.Term
  -> Domain.Type
  -> M (Syntax.Term Void, Syntax.MetaSolutions)
checkTopLevel key term type_ = do
  context <- Context.empty key
  term' <- check context term type_
  metaSolutions <- checkMetaSolutions context
  let
    term'' = globaliseMetas (Resolution.unkeyed key) term'
  pure (term'', metaSolutions)

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

elaborated
  :: Context v
  -> Expected e
  -> Syntax.Term v
  -> Lazy Domain.Type
  -> M (e (Syntax.Term v))
elaborated context expected term typ =
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
elaborate context term expected = -- trace ("elaborate " <> show term :: Text) $
  case term of
    Presyntax.Var name ->
      case Context.lookupNameIndex name context of
        Nothing -> do
          maybeQualifiedName <-
            fetch $
              Query.ResolvedName
                (Context.resolutionKey context)
                name
          case maybeQualifiedName of
            Nothing -> do
              report $ Error.NotInScope name
              resultType <- Context.newMetaType context
              resultType' <- readback context resultType
              elaborated
                context
                expected
                (Syntax.App (Syntax.Global Builtin.fail) resultType')
                (Lazy $ pure resultType)

            Just qualifiedName -> do
              (type_, _) <- fetch $ Query.ElaboratedType qualifiedName
              type' <- lazy $ evaluate context $ Syntax.fromVoid type_
              elaborated
                context
                expected
                (Syntax.Global $ Name.Elaborated qualifiedName)
                type'

        Just i ->
          elaborated
            context
            expected
            (Syntax.Var i)
            (Context.lookupIndexType i context)

    Presyntax.Let name term' body -> do
      Inferred term'' typ <- infer context term'
      typ' <- force typ
      typ'' <- readback context typ'

      term''' <- lazy $ evaluate context term''
      (context', _) <- Context.extendDef context name term''' $ Lazy $ pure typ'

      body' <- elaborate context' body expected
      pure $ Syntax.Let name term'' typ'' <$> body'

    Presyntax.Pi name source domain -> do
      source' <- check context source Builtin.type_

      (context', _) <- Context.extend context name $ Lazy $ pure Builtin.type_

      domain' <- check context' domain Builtin.type_
      elaborated
        context
        expected
        (Syntax.Pi name source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Fun source domain -> do
      source' <- check context source Builtin.type_
      domain' <- check context domain Builtin.type_
      elaborated
        context
        expected
        (Syntax.Fun source' domain')
        (Lazy $ pure Builtin.type_)

    Presyntax.Lam name body ->
      let
        inferIt = do
          source <- Context.newMetaType context
          source' <- readback context source
          (context', _) <- Context.extend context name (Lazy $ pure source)
          Inferred body' domain <- infer context' body
          type_ <- lazy $ do
            domain' <- force domain
            domain'' <- readback context' domain'
            pure
              $ Domain.Pi name (Lazy $ pure source)
              $ Domain.Closure (Context.toEvaluationEnvironment context) domain''

          elaborated
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
              source'' <- readback context source'
              (context', var) <- Context.extend context name source

              domain <-
                Evaluation.evaluateClosure
                  domainClosure
                  (Lazy $ pure $ Domain.var var)
              body' <- check context' body domain
              pure $ Checked (Syntax.Lam name source'' body')

            Domain.Fun source domain -> do
              source' <- force source
              source'' <- readback context source'
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
          elaborated
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

    Presyntax.Wildcard -> do
      type_ <- Context.newMetaType context
      term' <- Context.newMeta type_ context
      term'' <- readback context term'
      elaborated context expected term'' $ Lazy $ pure type_

-------------------------------------------------------------------------------
-- Meta solutions

checkMetaSolutions
  :: Context v
  -> M Syntax.MetaSolutions
checkMetaSolutions context = do
  metaVars <- liftIO $ readIORef $ Context.metas context
  flip HashMap.traverseWithKey (Meta.vars metaVars) $ \index var ->
    case var of
      Meta.Unsolved type_ -> do
        report $
          Error.UnsolvedMetaVariable
            (Resolution.unkeyed $ Context.resolutionKey context)
            index
        pure (Syntax.App (Syntax.Global Builtin.fail) type_, type_)

      Meta.Solved solution type_ ->
        pure (solution, type_)

globaliseMetas
  :: Name.Qualified
  -> Syntax.Term v
  -> Syntax.Term v
globaliseMetas global term = case term of
  Syntax.Var _ ->
    term

  Syntax.Global _ ->
    term

  Syntax.Meta index ->
    Syntax.Global $ Name.Meta global index

  Syntax.Let name term' type_ body ->
    Syntax.Let
      name
      (globaliseMetas global term')
      (globaliseMetas global type_)
      (globaliseMetas global body)

  Syntax.Pi name source domain ->
    Syntax.Pi name (globaliseMetas global source) (globaliseMetas global domain)

  Syntax.Fun source domain ->
    Syntax.Fun (globaliseMetas global source) (globaliseMetas global domain)

  Syntax.Lam name argType body ->
    Syntax.Lam name (globaliseMetas global argType) (globaliseMetas global body)

  Syntax.App function argument ->
    Syntax.App (globaliseMetas global function) (globaliseMetas global argument)

-------------------------------------------------------------------------------

evaluate
  :: Context v
  -> Syntax.Term v
  -> M Domain.Value
evaluate context =
  Evaluation.evaluate (Context.toEvaluationEnvironment context)

readback :: Context v -> Domain.Value -> M (Syntax.Term v)
readback context =
  Readback.readback (Context.toReadbackEnvironment context)
