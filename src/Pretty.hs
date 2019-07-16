{-# language OverloadedStrings #-}
module Pretty where

import Protolude

import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text.Prettyprint.Doc

import Index
import qualified Meta
import Name (Name(Name))
import qualified Syntax
import Syntax.Telescope (Telescope)
import qualified Syntax.Telescope as Telescope

-------------------------------------------------------------------------------
-- Pretty-printing environments

data Environment v = Environment
  { varNames :: Seq Name
  , usedNames :: HashSet Name
  }

extend :: Environment v -> Name -> (Environment (Succ v), Name)
extend env name@(Name text) =
  go (name : [Name $ text <> show (i :: Int) | i <- [0..]])
  where
    go (name':names)
      | name' `HashSet.member` usedNames env =
        go names
      | otherwise =
        (env
          { varNames = varNames env Seq.|> name'
          , usedNames = HashSet.insert name' (usedNames env)
          }
        , name'
        )
    go [] = panic "Pretty.extend"

empty :: Environment Void
empty = Environment
  { varNames = mempty
  , usedNames = mempty
  }

-------------------------------------------------------------------------------

prettyTerm :: Int -> Environment v -> Syntax.Term v -> Doc ann
prettyTerm prec env term = case term of
  Syntax.Var (Index i) ->
    pretty $
      Seq.index (varNames env) (Seq.length (varNames env) - i - 1)

  Syntax.Global g ->
    pretty g

  Syntax.Con c ->
    pretty c

  Syntax.Meta (Meta.Index i) ->
    pretty
      ("?" <> show i :: Text)

  Syntax.Let name term' typ body ->
    prettyParen (prec > letPrec) $
      let
        (env', name') = extend env name
      in
      "let"
      <> line <> indent 2
        (pretty name' <+> ":" <+> prettyTerm 0 env typ
        <> line <> pretty name' <+> "=" <+> prettyTerm 0 env term'
        )
      <> line <> "in"
      <> line <> prettyTerm letPrec env' body

  Syntax.Pi {} ->
    prettyParen (prec > funPrec) $
      prettyPiTerm env term

  Syntax.Fun source domain ->
    prettyParen (prec > funPrec) $
      prettyTerm (funPrec + 1) env source <+> "->" <+> prettyTerm funPrec env domain

  Syntax.Lam {} ->
    prettyParen (prec > lamPrec) $
      "\\" <> prettyLamTerm env term

  Syntax.App t1 plicity t2 ->
    prettyParen (prec > appPrec) $
      prettyTerm appPrec env t1 <+> pretty plicity <> prettyTerm (appPrec + 1) env t2

  Syntax.Case scrutinee branches ->
    prettyParen (prec > casePrec) $
      "case" <+> prettyTerm 0 env scrutinee <+> "of" <> line <>
        indent 2
          (vcat
            [ pretty constr <+> prettyBranch env tele
            | Syntax.Branch constr tele <- branches
            ]
          )

prettyLamTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyLamTerm env term = case term of
  Syntax.Lam name typ plicity scope ->
    let
      (env', name') = extend env name
    in
    pretty plicity <> lparen <> pretty name' <+> ":" <+> prettyTerm 0 env typ <> rparen
    <> prettyLamTerm env' scope

  t ->
    "." <+> prettyTerm lamPrec env t

prettyPiTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyPiTerm env term = case term of
  Syntax.Pi name typ plicity scope ->
    let
      (env', name') = extend env name
    in
    pretty plicity <> lparen <> pretty name' <+> ":" <+> prettyTerm 0 env typ <> rparen
    <> prettyPiTerm env' scope

  t ->
    " ->" <+> prettyTerm funPrec env t

prettyBranch
  :: Environment v
  -> Telescope Syntax.Type Syntax.Term v
  -> Doc ann
prettyBranch env tele =
  case tele of
    Telescope.Empty body ->
      "->" <> line <> indent 2 (prettyTerm casePrec env body)

    Telescope.Extend name type_ plicity tele' ->
      let
        (env', name') = extend env name
      in
      pretty plicity <> "(" <> pretty name' <+> ":" <+> prettyTerm 0 env type_ <> ")" <+>
      prettyBranch env' tele'

-------------------------------------------------------------------------------

prettyDefinition :: Pretty name => name -> Syntax.Definition -> Doc ann
prettyDefinition name def =
  case def of
    Syntax.TypeDeclaration type_ ->
      pretty name <+> ":" <+> prettyTerm 0 Pretty.empty type_

    Syntax.ConstantDefinition term ->
      pretty name <+> "=" <+> prettyTerm 0 Pretty.empty term

    Syntax.DataDefinition tele ->
      "data" <+> pretty name <+> prettyConstructorDefinitions Pretty.empty tele

prettyConstructorDefinitions
  :: Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> Doc ann
prettyConstructorDefinitions env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) ->
      "where" <> line <>
      indent 2
        (vcat
          [ pretty constr <+> ":" <+> prettyTerm 0 env type_
          | (constr, type_) <- constrs
          ]
        )

    Telescope.Extend name type_ plicity tele' ->
      let
        (env', name') = extend env name
      in
      pretty plicity <> "(" <> pretty name' <+> ":" <+> prettyTerm 0 env type_ <> ")" <+>
      prettyConstructorDefinitions env' tele'

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
