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

public export
replace : Env ctx a -> Elem nm ctx -> a -> Env ctx a
replace (env :< x) Here y = env :< y
replace (env :< x) (There idx) y = replace env idx y :< x

public export
replaceSame : {env : Env ctx a} ->
              {idx : Elem v ctx} ->
              get (replace env idx x) idx = x
replaceSame {env = env :< _} {idx = Here} = Refl
replaceSame {env = env :< _} {idx = There idx} = replaceSame {idx}

public export
replaceDiff : {env : Env ctx a} ->
              {i : Elem v ctx} ->
              {j : Elem u ctx} ->
              Not (i = j) ->
              get (replace env i x) j = get env j
replaceDiff {env = env :< _} {i = Here} {j = Here} nij = absurd $ nij Refl
replaceDiff {env = env :< _} {i = Here} {j = There j} nij = Refl
replaceDiff {env = env :< _} {i = There i} {j = Here} nij = Refl
replaceDiff {env = env :< _} {i = There i} {j = There j} nij = replaceDiff {i} {j} (nij . (\Refl => Refl))

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

    public export
    indEnvMiss : {i : Elem v ctx} ->
                 {j : Elem u ctx} ->
                 Not (x = y) ->
                 get (indEnv x y i) j = x ->
                 Not (i = j)
    indEnvMiss {i = Here} {j = Here} nxy prf Refl = nxy $ sym prf
    indEnvMiss {i = There i} {j = There i} nxy prf Refl = indEnvMiss {i} {j = i} nxy prf Refl

    public export
    replaceConstInd : {idx : Elem v ctx} -> replace (constEnv x) idx y = indEnv x y idx
    replaceConstInd {idx = Here} = Refl
    replaceConstInd {idx = There idx} = cong (:< x) $ replaceConstInd {idx}

    public export
    replaceIndConst : {idx : Elem v ctx} -> replace (indEnv x y idx) idx x = constEnv x
    replaceIndConst {idx = Here} = Refl
    replaceIndConst {idx = There idx} = cong (:< x) $ replaceIndConst {idx}

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
