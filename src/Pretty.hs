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
import qualified Syntax

-------------------------------------------------------------------------------
-- Pretty-printing environments

data Environment v = Environment
  { varNames :: Seq Text
  , usedNames :: HashSet Text
  }

extend :: Environment v -> Text -> (Environment (Succ v), Text)
extend env name = go (name : [name <> show (i :: Int) | i <- [0..]])
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
-- Pretty-printing environments

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

  Syntax.Let name typ (Scope body) ->
    prettyParen (prec > letPrec) $
      let
        (env', name') = extend env name
      in
      "let"
      <> line <> indent 2 (pretty name' <+> "=" <+> prettyTerm 0 env typ)
      <> line <> "in"
      <> line <> prettyTerm letPrec env' body

  Syntax.Pi name typ (Scope domain) ->
    prettyParen (prec > funPrec) $
      let
        (env', name') = extend env name
      in
      lparen <> pretty name' <+> ":" <+> prettyTerm 0 env typ <> rparen
      <+> "->"
      <+> prettyTerm funPrec env' domain

  Syntax.Fun source domain ->
    prettyParen (prec > funPrec) $
      prettyTerm (funPrec + 1) env source <+> "->" <+> prettyTerm funPrec env domain

  Syntax.Lam name (Scope body) ->
    prettyParen (prec > lamPrec) $
      let
        (env', name') = extend env name
      in
      "\\" <> pretty name' <> "." <+> prettyTerm lamPrec env' body

  Syntax.App t1 t2 ->
    prettyParen (prec > appPrec) $
      prettyTerm appPrec env t1 <+> prettyTerm (appPrec + 1) env t2

prettyParen :: Bool -> Doc a -> Doc a
prettyParen True doc = lparen <> doc <> rparen
prettyParen False doc = doc

funPrec, appPrec, lamPrec, letPrec :: Int
funPrec = 0
appPrec = 10
lamPrec = 0
letPrec = 0
