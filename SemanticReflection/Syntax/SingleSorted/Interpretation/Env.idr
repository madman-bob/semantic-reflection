module Syntax.SingleSorted.Interpretation.Env

import public Data.SnocList.Elem

%default total

||| The names of the variables available for an expression
public export
Context : Type
Context = SnocList String

||| An anonymous context of length n
public export
anonCtx : Nat -> Context
anonCtx 0 = [<]
anonCtx (S n) = anonCtx n :< ""

||| An environment in a context, for a type
|||
||| Assigns a value to each of the free variables.
public export
data Env : Context -> Type -> Type where
    Lin : Env [<] a
    (:<) : Env ctx a -> a -> Env (ctx :< nm) a

%name Env env

public export
Functor (Env ctx) where
    map f [<] = [<]
    map f (env :< x) = map f env :< f x

public export
get : Env ctx a -> Elem nm ctx -> a
get (env :< x) Here = x
get (env :< _) (There idx) = get env idx
