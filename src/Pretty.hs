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
import Telescope (Telescope)
import qualified Telescope

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

  Syntax.App t1 t2 ->
    prettyParen (prec > appPrec) $
      prettyTerm appPrec env t1 <+> prettyTerm (appPrec + 1) env t2

prettyLamTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyLamTerm env term = case term of
  Syntax.Lam name typ scope ->
    let
      (env', name') = extend env name
    in
    lparen <> pretty name' <+> ":" <+> prettyTerm 0 env typ <> rparen
    <> prettyLamTerm env' scope

  t ->
    "." <+> prettyTerm lamPrec env t

prettyPiTerm :: Environment v -> Syntax.Term v -> Doc ann
prettyPiTerm env term = case term of
  Syntax.Pi name typ scope ->
    let
      (env', name') = extend env name
    in
    lparen <> pretty name' <+> ":" <+> prettyTerm 0 env typ <> rparen
    <> prettyPiTerm env' scope

  t ->
    " ->" <+> prettyTerm funPrec env t

-------------------------------------------------------------------------------

prettyDefinition :: Pretty name => name -> Syntax.Definition -> Doc ann
prettyDefinition name def =
  case def of
    Syntax.TypeDeclaration type_ ->
      pretty name <+> ":" <+> prettyTerm 0 Pretty.empty type_

    Syntax.ConstantDefinition term ->
      pretty name <+> "=" <+> prettyTerm 0 Pretty.empty term

    Syntax.DataDefinition tele ->
      "data" <+> pretty name <+> prettyTelescope Pretty.empty tele

prettyTelescope
  :: Environment v
  -> Telescope Syntax.Type Syntax.ConstructorDefinitions v
  -> Doc ann
prettyTelescope env tele =
  case tele of
    Telescope.Empty (Syntax.ConstructorDefinitions constrs) ->
      "where" <> line <>
      indent 2
        (vcat
          [ pretty constr <+> ":" <+> prettyTerm 0 env type_
          | (constr, type_) <- constrs
          ]
        )

    Telescope.Extend name type_ tele' ->
      let
        (env', name') = extend env name
      in
      "(" <> pretty name' <+> ":" <+> prettyTerm 0 env type_ <> ")" <+>
      prettyTelescope env' tele'

-------------------------------------------------------------------------------

prettyParen :: Bool -> Doc a -> Doc a
prettyParen True doc = lparen <> doc <> rparen
prettyParen False doc = doc

funPrec, appPrec, lamPrec, letPrec :: Int
funPrec = 0
appPrec = 10
lamPrec = 0
letPrec = 0
