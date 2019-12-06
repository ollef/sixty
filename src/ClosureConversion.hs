{-# language ScopedTypeVariables #-}

module ClosureConversion where

import Protolude

import Monad
import Plicity
import qualified Syntax.ClosureConverted as ClosureConverted
import qualified Syntax.LambdaLifted as LambdaLifted

{-
cc f = CL f0 n
cc (f e1 .. em)
  | m == n = f e1 .. em
  | m < n = Ref (CL fm (n - m) e1 .. em)
  | m > n = apply (m - n) (f e1 .. en) sizeof(en+1) .. sizeof(em) en+1 .. em
cc (x e1 .. em) = applym x sizeof(e1) .. sizeof(em) e1 .. em

fm xthis xm+1size .. xnsize xm+1 .. xn = case xthis of
  CL _ _ y1 .. ym -> f y1 .. ym xm+1 .. xn

applym xthis x1size .. xmsize x1 .. xm = case xthis of
  CL funknown n
    | m == n -> funknown xthis x1size .. xmsize x1 .. xm
    | m < n -> Ref (CL pap(n-m),m (n - m) xthis x1size .. xmsize x1 .. xm)
    | m > n -> apply(m-n) (funknown xthis x1size .. xnsize x1 .. xn) xn+1size .. xmsize xn+1 .. xm

papk,m xthis x1size .. xksize x1 .. xk = case xthis of
  CL _ _ ythat y1size .. ymsize y1 .. ym -> apply(m+k) ythat y1size .. ymsize x1size .. xksize y1 .. ym x1 .. xk
-}

closureConvert :: forall v. LambdaLifted.Term v -> [(Plicity, ClosureConverted.Term v)] -> M (ClosureConverted.Term v)
closureConvert term args =
  case term of
    LambdaLifted.Var v ->
      pure $ unknown $ ClosureConverted.Var v

    LambdaLifted.Global global ->
      known global

    LambdaLifted.Con con conArgs ->
      undefined

    LambdaLifted.Let binding term type_ body ->
      undefined

    LambdaLifted.Pi binding domain plicity target ->
      undefined

    LambdaLifted.Fun domain plicity target ->
      undefined

    LambdaLifted.App fun plicity arg -> do
      arg' <- closureConvert arg []
      closureConvert fun ((plicity, arg'):args)

    LambdaLifted.Case scrutinee branches defaultBranch ->
      undefined

  where
    unknown :: ClosureConverted.Term v -> M (ClosureConverted.Term v)
    unknown term' =
      case args of
        [] ->
          pure term'

        _ ->
          pure $ ClosureConverted.ApplyUnknown term' args -- TODO types

    known :: ClosureConverted.Term v -> M (ClosureConverted.Term v)
    known =
      undefined
