{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Low.Pretty where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Kind
import qualified Data.Sequence as Seq
import qualified Data.Text.Unsafe as Text
import Index
import qualified Low.Syntax as Syntax
import Name (Name (Name))
import qualified Name
import Prettyprinter
import Protolude hiding (repr)
import Query (Query)
import qualified Query
import qualified Query.Mapped as Mapped
import Rock
import qualified Scope

-------------------------------------------------------------------------------
-- Pretty-printing environments

data Environment (v :: Data.Kind.Type) = Environment
  { varNames :: Seq Name.Surface
  , usedNames :: HashMap Name.Surface (Maybe Scope.Entry)
  , importedConstructorAliases :: HashMap Name.QualifiedConstructor (HashSet Name.Surface)
  , importedAliases :: HashMap Name.Qualified (HashSet Name.Surface)
  }

extend :: Environment v -> Name -> (Environment (Succ v), Name.Surface)
extend env (Name name) =
  go (Name.Surface name : [Name.Surface $ name <> show (i :: Int) | i <- [0 ..]])
  where
    go (name' : names)
      | name' `HashMap.member` usedNames env = go names
      | otherwise =
          ( env
              { varNames = varNames env Seq.|> name'
              , usedNames = HashMap.insert name' Nothing (usedNames env)
              }
          , name'
          )
    go [] = panic "Pretty.extend"

empty :: Environment Void
empty =
  Environment
    { varNames = mempty
    , usedNames = mempty
    , importedConstructorAliases = mempty
    , importedAliases = mempty
    }

emptyM :: (MonadFetch Query m) => Name.Module -> m (Environment Void)
emptyM module_ = do
  importedNames <- fetch $ Query.ImportedNames module_ Mapped.Map
  (localScope, _) <- fetch $ Query.ModuleScope module_
  (constrAliases, aliases) <- fetch $ Query.NameAliases module_
  pure
    Environment
      { varNames = mempty
      , usedNames = fmap Just $ importedNames <> localScope
      , importedConstructorAliases = constrAliases
      , importedAliases = aliases
      }

-------------------------------------------------------------------------------

prettyTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyTerm env = \case
  Syntax.Operand operand -> prettyOperand env operand
  term@Syntax.Let {} ->
    line <> indent 2 (prettySeq env term)
  term@Syntax.Seq {} ->
    line <> indent 2 (prettySeq env term)
  Syntax.Case scrutinee branches defaultBranch ->
    "case"
      <+> prettyOperand env scrutinee
      <+> "of"
      <> line
      <> indent
        2
        ( vcat $
            (prettyBranch env <$> branches)
              <> [ "_" <+> "->" <> prettyTerm env branch
                 | Just branch <- [defaultBranch]
                 ]
        )
  Syntax.Call function args ->
    "call"
      <+> prettyLiftedGlobal env function
      <+> commaSep (prettyOperand env <$> args)
  Syntax.StackAllocate operand ->
    "stack_allocate" <+> prettyOperand env operand
  Syntax.HeapAllocate con operand ->
    "heap_allocate" <+> commaSep [prettyConstr env con, prettyOperand env operand]
  Syntax.HeapPayload operand ->
    "heap_payload" <+> prettyOperand env operand
  Syntax.PointerTag operand ->
    "pointer_tag" <+> prettyOperand env operand
  Syntax.Offset operand1 operand2 ->
    prettyOperand env operand1 <+> "+" <+> prettyOperand env operand2
  Syntax.Copy dst src size ->
    "copy" <+> commaSep [prettyOperand env dst, prettyOperand env src, prettyOperand env size]
  Syntax.Store dst src repr ->
    "store" <+> commaSep [prettyOperand env dst, pretty repr <+> prettyOperand env src]
  Syntax.Load src repr ->
    "load" <+> pretty repr <+> prettyOperand env src

prettySeq :: Environment v -> Syntax.Term v -> Doc ann
prettySeq env = \case
  Syntax.Let passBy name term body -> do
    let (env', name') = extend env name
    "let"
      <+> pretty passBy
      <+> pretty name'
      <+> "="
      <+> prettyTerm env term
      <> line
      <> prettySeq env' body
  Syntax.Seq term1 term2 ->
    prettyTerm env term1
      <> line
      <> prettySeq env term2
  term -> prettyTerm env term

commaSep :: [Doc ann] -> Doc ann
commaSep = hcat . punctuate (comma <> space)

prettyOperand :: Environment v -> Syntax.Operand v -> Doc ann
prettyOperand env = \case
  Syntax.Var (Index i) ->
    pretty $
      Seq.index (varNames env) (Seq.length (varNames env) - i - 1)
  Syntax.Global global -> prettyLiftedGlobal env global
  Syntax.Literal lit -> pretty lit
  Syntax.Representation repr -> pretty repr
  Syntax.Tag constr -> prettyConstr env constr
  Syntax.Undefined repr -> pretty repr <+> "undefined"

prettyGlobal :: Environment v -> Name.Qualified -> Doc ann
prettyGlobal env global = do
  let aliases =
        sortOn (\(Name.Surface name) -> Text.lengthWord8 name) $
          filter (unambiguous env) $
            HashSet.toList $
              HashMap.lookupDefault mempty global $
                importedAliases env
  case aliases of
    [] -> pretty global
    alias : _ -> pretty alias

prettyLiftedGlobal :: Environment v -> Name.Lifted -> Doc ann
prettyLiftedGlobal env = \case
  Name.Lifted global 0 -> prettyGlobal env global
  Name.Lifted global n -> prettyGlobal env global <> "$" <> pretty n

prettyConstr :: Environment v -> Name.QualifiedConstructor -> Doc ann
prettyConstr env constr = do
  let aliases =
        sortOn (\(Name.Surface name) -> Text.lengthWord8 name) $
          filter (unambiguous env) $
            HashSet.toList $
              HashMap.lookupDefault mempty constr $
                importedConstructorAliases env
  case aliases of
    [] -> pretty constr
    alias : _ -> pretty alias

unambiguous :: Environment v -> Name.Surface -> Bool
unambiguous env name =
  case HashMap.lookupDefault Nothing name $ usedNames env of
    Nothing -> True
    Just (Scope.Name _) -> True
    Just (Scope.Constructors cs ds) -> HashSet.size cs + HashSet.size ds == 1
    Just (Scope.Ambiguous _ _) -> False

prettyBranch
  :: Environment v
  -> Syntax.Branch v
  -> Doc ann
prettyBranch env = \case
  Syntax.ConstructorBranch constr body ->
    prettyConstr env constr <+> "->" <> prettyTerm env body
  Syntax.LiteralBranch lit body ->
    pretty lit <+> "->" <> prettyTerm env body

-------------------------------------------------------------------------------

prettyDefinition :: Environment Void -> Name.Lifted -> Syntax.Definition -> Doc ann
prettyDefinition env name = \case
  Syntax.ConstantDefinition repr term ->
    prettyLiftedGlobal env name <+> pretty repr <+> "=" <+> prettyTerm env term
  Syntax.FunctionDefinition function ->
    prettyLiftedGlobal env name <+> "=" <+> "\\" <> prettyFunction env function

prettyFunction :: Environment v -> Syntax.Function v -> Doc ann
prettyFunction env = \case
  Syntax.Body passReturnBy body -> " ->" <+> pretty passReturnBy <+> prettyTerm env body
  Syntax.Parameter name passArgBy function' -> do
    let (env', name') = extend env name
    "("
      <> pretty passArgBy
      <+> pretty name'
      <> ")"
      <> prettyFunction env' function'
