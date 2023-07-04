module Syntax.SingleSorted.Interpretation.Env.Any

import public Data.DPair

import public Syntax.SingleSorted.Interpretation.Env

%default total

public export
data AnyVar : (0 ctx : Context) -> (0 p : forall nm. Elem nm ctx -> Type) -> Type where
    Here : {0 p : forall n. Elem n (ctx :< m) -> Type} ->
           p Here ->
           AnyVar (ctx :< m) p
    There : {0 p : forall n. Elem n (ctx :< m) -> Type} ->
            AnyVar ctx (p  . There)->
            AnyVar (ctx :< m) p

%name AnyVar px

public export
Any : (env : Env ctx a) -> (p : a -> Type) -> Type
Any env p = AnyVar ctx $ \idx => p (get env idx)

export
getAny : {ctx : Context} ->
         {0 p : forall nm. Elem nm ctx -> Type} ->
         AnyVar ctx p ->
         Exists $ \nm => (idx : Elem nm ctx ** p idx)
getAny {ctx = ctx :< m} (Here px) = Evidence m (Here ** px)
getAny {ctx = ctx :< m} (There anyVar) = do
    let Evidence nm (idx ** px) = getAny {ctx} anyVar
    Evidence nm (There idx ** px)
