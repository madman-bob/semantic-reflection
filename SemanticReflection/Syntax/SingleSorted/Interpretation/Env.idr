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

namespace ConstEnv
    public export
    constEnv : {ctx : Context} ->
               a ->
               Env ctx a
    constEnv {ctx = [<]} x = [<]
    constEnv {ctx = _ :< _} x = constEnv x :< x

    public export
    constEnvConst : {idx : Elem v ctx} ->
                    get (constEnv x) idx = x
    constEnvConst {idx = Here} = Refl
    constEnvConst {idx = There idx} = constEnvConst {idx}

namespace IndicatorEnv
    public export
    indEnv : {ctx : Context} ->
             a ->
             a ->
             Elem v ctx ->
             Env ctx a
    indEnv x y Here = constEnv x :< y
    indEnv x y (There idx) = indEnv x y idx :< x

    public export
    indEnvSame : {idx : Elem v ctx} -> get (indEnv x y idx) idx = y
    indEnvSame {idx = Here} = Refl
    indEnvSame {idx = There idx} = indEnvSame {idx}

    public export
    indEnvDiff : {i : Elem v ctx} ->
                 {j : Elem u ctx} ->
                 Not (i = j) ->
                 get (indEnv x y i) j = x
    indEnvDiff {i = Here} {j = Here} nij = absurd $ nij Refl
    indEnvDiff {i = Here} {j = There j} nij = constEnvConst
    indEnvDiff {i = There i} {j = Here} nij = Refl
    indEnvDiff {i = There i} {j = There j} nij = indEnvDiff {i} {j} (nij . (\Refl => Refl))

    public export
    indEnvMatch : {i : Elem v ctx} ->
                  {j : Elem u ctx} ->
                  Not (x = y) ->
                  get (indEnv x y i) j = y ->
                  (v = u, i = j)
    indEnvMatch {i = Here} {j = Here} nxy prf = (Refl, Refl)
    indEnvMatch {i = Here} {j = There j} nxy prf = absurd $ nxy $ trans (sym constEnvConst) prf
    indEnvMatch {i = There i} {j = Here} nxy prf = absurd $ nxy prf
    indEnvMatch {i = There i} {j = There j} nxy prf with (indEnvMatch {i} {j} nxy prf)
      indEnvMatch {i = There i} {j = There i} nxy prf | (Refl, Refl) = (Refl, Refl)

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
