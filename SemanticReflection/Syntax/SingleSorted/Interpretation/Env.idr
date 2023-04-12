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

||| A reversed environment in a context, for a type
|||
||| Usually viewed as a collection of arguments, before the desired context is
||| known.
public export
data ConsEnv : List String -> Type -> Type where
    Nil : ConsEnv [] a
    (::) : a -> ConsEnv ctx a -> ConsEnv (nm :: ctx) a

%name ConsEnv env

||| Extend an environment by a collection of arguments
public export
(<><) : Env ctx a -> ConsEnv ctx' a -> Env (ctx <>< ctx') a
env <>< [] = env
env <>< (x :: rest) = (env :< x) <>< rest

||| Attempt to interpret a collection of arguments as an environment, in a desired
||| context
public export
collect : {ctx : Context} ->
          ConsEnv nms a ->
          Maybe (Env ctx a)
collect env = coerce $ [<] <>< env
  where
    coerce : {ctx : Context} ->
             {0 nms : Context} ->
             Env nms a ->
             Maybe (Env ctx a)
    coerce {ctx = [<]} [<] = Just [<]
    coerce {ctx = [<]} (env :< x) = Nothing
    coerce {ctx = ctx :< nm} [<] = Nothing
    coerce {ctx = ctx :< nm} (env :< x) = map (:< x) (coerce {ctx} env)

public export
length : ConsEnv ctx a -> Nat
length [] = 0
length (_ :: env) = S (length env)
