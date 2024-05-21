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
import Low.PassBy (PassBy)
import qualified Low.PassBy as PassBy
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

prettyTerm :: Int -> Environment v -> Syntax.Term v -> Doc ann
prettyTerm prec env = \case
  Syntax.Operand operand -> prettyOperand env operand
  term@Syntax.Let {} ->
    line
      <> indent
        2
        ( prettyParen
            (prec > letPrec)
            (prettySeq env term)
        )
  term@Syntax.Seq {} ->
    line
      <> indent
        2
        ( prettyParen
            (prec > letPrec)
            (prettySeq env term)
        )
  Syntax.Case scrutinee branches defaultBranch ->
    prettyParen (prec > casePrec) $
      "case"
        <+> prettyOperand env scrutinee
        <+> "of"
          <> line
          <> indent
            2
            ( vcat $
                (prettyBranch env <$> branches)
                  <> [ "_" <+> "->" <> prettyTerm casePrec env branch
                     | Just branch <- [defaultBranch]
                     ]
            )
  Syntax.Call function args ->
    prettyLiftedGlobal env function <> encloseSep lparen rparen comma (prettyOperand env <$> args)
  Syntax.StackAllocate operand ->
    "#stack_allocate" <> lparen <> prettyOperand env operand <> rparen
  Syntax.HeapAllocate con operand ->
    "#heap_allocate" <> encloseSep lparen rparen comma [prettyConstr env con, prettyOperand env operand]
  Syntax.Dereference operand ->
    "*" <> prettyOperand env operand
  Syntax.PointerTag operand ->
    "#pointer_tag" <> lparen <> prettyOperand env operand <> rparen
  Syntax.Offset operand1 operand2 ->
    prettyOperand env operand1 <+> "+" <+> prettyOperand env operand2
  Syntax.Copy dst src size ->
    "#copy" <> encloseSep lparen rparen comma [prettyOperand env dst, prettyOperand env src, prettyOperand env size]
  Syntax.Store dst src repr ->
    "#store" <> encloseSep lparen rparen comma [prettyOperand env dst, pretty repr <+> prettyOperand env src]
  Syntax.Load src repr ->
    "#load" <> lparen <> pretty repr <+> prettyOperand env src <> rparen

prettySeq :: Environment v -> Syntax.Term v -> Doc ann
prettySeq env = \case
  Syntax.Let passBy name term body -> do
    let (env', name') = extend env name
    "let"
      <+> prettyPassBy passBy
      <+> pretty name'
      <+> "="
      <+> prettyTerm 0 env term
        <> ";"
        <> line
        <> prettySeq env' body
  Syntax.Seq term1 term2 ->
    prettyTerm (seqPrec + 1) env term1
      <> ";"
      <> line
      <> prettySeq env term2
  term -> prettyTerm 0 env term

prettyOperand :: Environment v -> Syntax.Operand v -> Doc ann
prettyOperand env = \case
  Syntax.Var (Index i) ->
    pretty $
      Seq.index (varNames env) (Seq.length (varNames env) - i - 1)
  Syntax.Global global -> prettyLiftedGlobal env global
  Syntax.Literal lit -> pretty lit
  Syntax.Representation repr -> pretty repr
  Syntax.Tag constr -> prettyConstr env constr

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

prettyPassBy :: PassBy -> Doc ann
prettyPassBy = \case
  PassBy.Value repr -> pretty repr
  PassBy.Reference -> "ref"

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
    prettyConstr env constr <+> "->" <> prettyTerm casePrec env body
  Syntax.LiteralBranch lit body ->
    pretty lit <+> "->" <> prettyTerm casePrec env body

-------------------------------------------------------------------------------

prettyDefinition :: (MonadFetch Query m) => Environment Void -> Name.Lifted -> Syntax.Definition -> m (Doc ann)
prettyDefinition env name def = do
  signature <- fetch $ Query.LowSignature name
  pure case (def, signature) of
    (Syntax.ConstantDefinition term, Syntax.ConstantSignature repr) ->
      prettyLiftedGlobal env name <+> pretty repr <+> "=" <> line <> indent 2 (prettyTerm 0 env term)
    (Syntax.ConstantDefinition _, _) -> panic "definition signature mismatch"
    (Syntax.FunctionDefinition function, Syntax.FunctionSignature passArgsBy passReturnBy) ->
      prettyLiftedGlobal env name <+> "=" <+> "\\" <> prettyFunction env passArgsBy passReturnBy function
    (Syntax.FunctionDefinition _, _) -> panic "definition signature mismatch"

prettyFunction :: Environment v -> [PassBy] -> PassBy -> Syntax.Function v -> Doc ann
prettyFunction env passArgsBy passReturnBy function = case (passArgsBy, function) of
  ([], Syntax.Body body) -> " ->" <+> prettyPassBy passReturnBy <+> prettyTerm 0 env body
  ([], _) -> panic "function signature mismatch"
  (passArgBy : passArgsBy', Syntax.Parameter name function') -> do
    let (env', name') = extend env name
    "("
      <> prettyPassBy passArgBy
      <+> pretty name'
        <> ")"
        <> prettyFunction env' passArgsBy' passReturnBy function'
  (_ : _, _) -> panic "function signature mismatch"

-------------------------------------------------------------------------------

prettyParen :: Bool -> Doc a -> Doc a
prettyParen True doc = lparen <> doc <> rparen
prettyParen False doc = doc

letPrec, seqPrec, casePrec :: Int
letPrec = 1
seqPrec = 0
casePrec = 1
