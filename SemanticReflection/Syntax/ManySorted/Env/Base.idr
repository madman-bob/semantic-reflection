module Syntax.ManySorted.Env.Base

%default total

||| The names and sorts of the variables available for an expression
|||
||| For example, suppose we are using Nat as our sorts.
||| Then for a context with variables `x` and `y`, of sorts 1 and 2, we can write:
|||   SomeCtx : Context Nat
|||   SomeCtx = [<"x" :! 1, "y" :! 2]
|||
||| We can also write:
|||   SomeCtx : Context Nat
|||   SomeCtx = `[x : 1; y : 2]
public export
Context : Type -> Type
Context s = SnocList (String, s)

export infix 10 :!

public export
(:!) : String -> s -> (String, s)
nm :! a = (nm, a)

||| An environment in a context, and type universe
|||
||| Assigns a value of the appropriate type to each of the variables.
|||
||| For example, in
|||   someEnv : Env `[x : 1; y : 2] (`Vect` String)
|||   someEnv = [<["Hello, world"], ["Lorem", "ipsum"]]
||| we assign `x` a `Vect 1 String`, and `y` a `Vect 2 String`.
public export
data Env : Context s -> (u : s -> Type) -> Type where
    Lin : Env [<] u
    (:<) : Env ctx u -> u a -> Env (ctx :< (nm :! a)) u

%name Env env

public export
map : (f : forall a. u a -> v a) ->
      Env ctx u ->
      Env ctx v
map f [<] = [<]
map f (env :< x) = map f env :< f x

||| A variable reference in a context, of given sort
|||
||| For example, suppose we are using Nat as our sorts.
||| Then a `Var SomeCtx 2` is a reference to a variable in that context of sort 2.
public export
data Var : Context s -> s -> Type where
    Here : Var (ctx :< (nm :! a)) a
    There : Var ctx a -> Var (ctx :< (nm :! b)) a

%name Var var

public export
get : Env ctx u -> Var ctx a -> u a
get (env :< x) Here = x
get (env :< x) (There var) = get env var

export
getMap : {0 u : s -> Type} ->
         {0 v : s -> Type} ->
         {env : Env ctx u} ->
         {var : Var ctx a} ->
         {0 f : forall a. u a -> v a} ->
         get (map f env) var = f (get env var)
getMap {env = env :< x} {var = Here} = Refl
getMap {env = env :< x} {var = There var} = getMap {env} {var}

public export
varEnv : {ctx : Context s} ->
         Env ctx (Var ctx)
varEnv {ctx = [<]} = [<]
varEnv {ctx = ctx :< (nm, a)} = (map There $ varEnv {ctx}) :< Here

export
getVarEnv : {var : Var ctx a} ->
            get Base.varEnv var = var
getVarEnv {var = Here} = Refl
getVarEnv {var = There var} = trans getMap $ cong There $ getVarEnv {var}

namespace Named
    ||| A named variable reference in a context, of given sort
    |||
    ||| For example, suppose we are using Nat as our sorts.
    ||| Then a `Var SomeCtx "x" 2` is a reference to a variable "x" in that context of
    ||| sort 2.
    public export
    data NVar : (ctx : Context s) -> (nm : String) -> (a : s) -> Type where
        [search ctx nm, uniqueSearch]
        Here : NVar (ctx :< (nm :! a)) nm a
        There : NVar ctx nm a -> NVar (ctx :< (n :! b)) nm a

    public export
    %inline
    forgetName : NVar ctx nm a -> Var ctx a
    forgetName Here = Here
    forgetName (There x) = There (forgetName x)
