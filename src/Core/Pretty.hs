{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Core.Pretty where

import qualified Boxity
import Core.Binding (Binding)
import qualified Core.Binding as Binding
import Core.Bindings (Bindings)
import qualified Core.Bindings as Bindings
import Core.Domain.Pattern (Pattern)
import qualified Core.Domain.Pattern as Pattern
import qualified Core.Syntax as Syntax
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Kind
import qualified Data.OrderedHashMap as OrderedHashMap
import qualified Data.Sequence as Seq
import qualified Data.Text.Unsafe as Text
import Index
import Name (Name (Name))
import qualified Name
import Plicity
import Prettyprinter
import Protolude
import Query (Query)
import qualified Query
import qualified Query.Mapped as Mapped
import Rock
import qualified Scope
import Telescope (Telescope)
import qualified Telescope

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
      | name' `HashMap.member` usedNames env =
          go names
      | otherwise =
          ( env
              { varNames = varNames env Seq.|> name'
              , usedNames = HashMap.insert name' Nothing (usedNames env)
              }
          , name'
          )
    go [] =
      panic "Pretty.extend"

extendBinding :: Environment v -> Binding -> (Environment (Succ v), Name.Surface)
extendBinding env binding =
  extend env $ Binding.toName binding

extendBindings :: Environment v -> Bindings -> (Environment (Succ v), Name.Surface)
extendBindings env binding =
  extend env $ Bindings.toName binding

empty :: Environment Void
empty =
  Environment
    { varNames = mempty
    , usedNames = mempty
    , importedConstructorAliases = mempty
    , importedAliases = mempty
    }

emptyM :: MonadFetch Query m => Name.Module -> m (Environment Void)
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
prettyTerm prec env term =
  case term of
    Syntax.Var (Index i) ->
      pretty $
        Seq.index (varNames env) (Seq.length (varNames env) - i - 1)
    Syntax.Global global ->
      prettyGlobal env global
    Syntax.Con constr ->
      prettyConstr env constr
    Syntax.Lit lit ->
      pretty lit
    Syntax.Meta index ->
      pretty index
    Syntax.PostponedCheck index term' ->
      "postponed" <+> pretty index <+> "is" <+> prettyTerm prec env term'
    Syntax.Lets lets ->
      prettyParen (prec > letPrec) $
        "let"
          <> line
          <> indent 2 (prettyLets env lets)
    Syntax.Pi _ _ Implicit _ ->
      prettyParen (prec > funPrec) $
        "forall" <+> prettyPiTerm env Implicit term "."
    Syntax.Pi _ _ Explicit _ ->
      prettyParen (prec > funPrec) $
        prettyPiTerm env Explicit term " ->"
    Syntax.Pi binding type_ plicity scope ->
      prettyParen (prec > funPrec) $
        let (env', name) = extendBinding env binding
         in Plicity.prettyAnnotation plicity <> lparen <> pretty name
              <+> ":"
              <+> prettyTerm 0 env type_ <> rparen
              <+> "->"
              <+> prettyTerm funPrec env' scope
    Syntax.Fun domain plicity target ->
      prettyParen (prec > funPrec) $
        Plicity.prettyAnnotation plicity <> prettyTerm (funPrec + 1) env domain <+> "->" <+> prettyTerm funPrec env target
    Syntax.Lam {} ->
      prettyParen (prec > lamPrec) $
        "\\" <> prettyLamTerm env term
    Syntax.App t1 plicity t2 ->
      prettyParen (prec > appPrec) $
        prettyTerm appPrec env t1 <+> Plicity.prettyAnnotation plicity <> prettyTerm (appPrec + 1) env t2
    Syntax.Case scrutinee branches defaultBranch ->
      prettyParen (prec > casePrec) $
        "case"
          <+> prettyTerm 0 env scrutinee
          <+> "of"
            <> line
            <> indent
              2
              ( vcat $
                  case branches of
                    Syntax.ConstructorBranches constructorTypeName constructorBranches ->
                      [ prettyConstr env (Name.QualifiedConstructor constructorTypeName constr) <+> prettyBranch env tele
                      | (constr, (_, tele)) <- OrderedHashMap.toList constructorBranches
                      ]
                    Syntax.LiteralBranches literalBranches ->
                      [ pretty lit <+> "->" <+> prettyTerm 0 env body
                      | (lit, (_, body)) <- OrderedHashMap.toList literalBranches
                      ]
                    <> [ "_"
                        <+> "->"
                          <> line
                          <> indent 2 (prettyTerm casePrec env branch)
                       | Just branch <- [defaultBranch]
                       ]
              )
    Syntax.Spanned _ term' ->
      prettyTerm prec env term'

prettyGlobal :: Environment v -> Name.Qualified -> Doc ann
prettyGlobal env global = do
  let aliases =
        sortOn (\(Name.Surface name) -> Text.lengthWord16 name) $
          filter (unambiguous env) $
            HashSet.toList $
              HashMap.lookupDefault mempty global $
                importedAliases env

  case aliases of
    [] ->
      pretty global
    alias : _ ->
      pretty alias

prettyConstr :: Environment v -> Name.QualifiedConstructor -> Doc ann
prettyConstr env constr = do
  let aliases =
        sortOn (\(Name.Surface name) -> Text.lengthWord16 name) $
          filter (unambiguous env) $
            HashSet.toList $
              HashMap.lookupDefault mempty constr $
                importedConstructorAliases env

  case aliases of
    [] ->
      pretty constr
    alias : _ ->
      pretty alias

unambiguous :: Environment v -> Name.Surface -> Bool
unambiguous env name =
  case HashMap.lookupDefault Nothing name $ usedNames env of
    Nothing ->
      True
    Just (Scope.Name _) ->
      True
    Just (Scope.Constructors cs ds) ->
      HashSet.size cs + HashSet.size ds == 1
    Just (Scope.Ambiguous _ _) ->
      False

prettyLamTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyLamTerm env term =
  case term of
    Syntax.Lam bindings type_ plicity scope ->
      let (env', name) = extendBindings env bindings
       in Plicity.prettyAnnotation plicity <> lparen <> pretty name
            <+> ":"
            <+> prettyTerm 0 env type_
              <> rparen
              <> prettyLamTerm env' scope
    Syntax.Spanned _ term' ->
      prettyLamTerm env term'
    t ->
      "." <+> prettyTerm lamPrec env t

prettyPiTerm :: Environment v -> Plicity -> Syntax.Term v -> Doc ann -> Doc ann
prettyPiTerm env plicity term separator =
  case term of
    Syntax.Pi binding type_ plicity' scope
      | plicity == plicity' ->
          let (env', name) = extendBinding env binding
           in lparen <> pretty name
                <+> ":"
                <+> prettyTerm 0 env type_
                  <> rparen
                  <> prettyPiTerm env' plicity scope separator
    Syntax.Spanned _ term' ->
      prettyPiTerm env plicity term' separator
    t ->
      separator <+> prettyTerm funPrec env t

prettyLets :: Environment v -> Syntax.Lets v -> Doc ann
prettyLets env lets =
  case lets of
    Syntax.LetType binding type_ lets' ->
      let (env', name) = extendBinding env binding
       in pretty name
            <+> ":"
            <+> prettyTerm letPrec env type_
              <> line
              <> prettyLets env' lets'
    Syntax.Let _ index term lets' ->
      prettyTerm letPrec env (Syntax.Var index)
        <+> "="
        <+> prettyTerm letPrec env term
          <> line
          <> prettyLets env lets'
    Syntax.In term ->
      "in"
        <> line
        <> prettyTerm letPrec env term

prettyBranch
  :: Environment v
  -> Telescope Bindings Syntax.Type Syntax.Term v
  -> Doc ann
prettyBranch env tele =
  case tele of
    Telescope.Empty body ->
      "->" <> line <> indent 2 (prettyTerm casePrec env body)
    Telescope.Extend bindings type_ plicity tele' ->
      let (env', name) = extendBindings env bindings
       in Plicity.prettyAnnotation plicity <> "(" <> pretty name
            <+> ":"
            <+> prettyTerm 0 env type_ <> ")"
            <+> prettyBranch env' tele'

-------------------------------------------------------------------------------

prettyDefinition :: Environment Void -> Name.Qualified -> Syntax.Definition -> Doc ann
prettyDefinition env name def =
  case def of
    Syntax.TypeDeclaration type_ ->
      prettyGlobal env name <+> ":" <+> prettyTerm 0 env type_
    Syntax.ConstantDefinition term ->
      prettyGlobal env name <+> "=" <+> prettyTerm 0 env term
    Syntax.DataDefinition boxity tele ->
      Boxity.prettyAnnotation boxity "data" <+> prettyGlobal env name <+> prettyConstructorDefinitions env tele

prettyConstructorDefinitions
  :: Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> Doc ann
prettyConstructorDefinitions env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) ->
      "where"
        <> line
        <> indent
          2
          ( vcat
              [ pretty constr <+> ":" <+> prettyTerm 0 env type_
              | (constr, type_) <- OrderedHashMap.toList constrs
              ]
          )
    Telescope.Extend _ _ Implicit _ ->
      "forall" <+> prettyConstructorDefinitionsImplicit env tele
    Telescope.Extend binding type_ plicity tele' ->
      let (env', name) = extendBinding env binding
       in Plicity.prettyAnnotation plicity <> "(" <> pretty name
            <+> ":"
            <+> prettyTerm 0 env type_ <> ")"
            <+> prettyConstructorDefinitions env' tele'

prettyConstructorDefinitionsImplicit
  :: Environment v
  -> Telescope Binding Syntax.Type Syntax.ConstructorDefinitions v
  -> Doc ann
prettyConstructorDefinitionsImplicit env tele =
  case tele of
    Telescope.Empty _ ->
      prettyConstructorDefinitions env tele
    Telescope.Extend binding type_ Implicit tele' ->
      let (env', name) = extendBinding env binding
       in lparen <> pretty name
            <+> ":"
            <+> prettyTerm 0 env type_
              <> rparen
              <> prettyConstructorDefinitionsImplicit env' tele'
    Telescope.Extend _ _ _ _ ->
      "." <+> prettyConstructorDefinitions env tele

-------------------------------------------------------------------------------

prettyPattern :: Int -> Environment v -> Pattern -> Doc ann
prettyPattern prec env pattern_ =
  case pattern_ of
    Pattern.Wildcard ->
      "_"
    Pattern.Con constr [] ->
      prettyConstr env constr
    Pattern.Con constr patterns ->
      prettyParen (prec > appPrec) $
        hsep $
          prettyConstr env constr
            : [ Plicity.prettyAnnotation plicity <> prettyPattern (appPrec + 1) env pattern'
              | (plicity, pattern') <- patterns
              ]
    Pattern.Lit lit ->
      pretty lit

-------------------------------------------------------------------------------

prettyParen :: Bool -> Doc a -> Doc a
prettyParen True doc = lparen <> doc <> rparen
prettyParen False doc = doc

funPrec, appPrec, lamPrec, letPrec, casePrec :: Int
funPrec = 0
appPrec = 10
lamPrec = 0
letPrec = 0
casePrec = 0
