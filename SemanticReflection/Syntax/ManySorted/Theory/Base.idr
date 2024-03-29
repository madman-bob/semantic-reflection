module Syntax.ManySorted.Theory.Base

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term

%default total

public export
ISort : Context Type -> Type -> Type
ISort metaVars s = Env metaVars id -> s

public export
IContext : Context Type -> Type -> Type
IContext metaVars s = Context (ISort metaVars s)

public export
IEnv : Env metaVars Prelude.id -> IContext metaVars s -> (s -> Type) -> Type
IEnv metaEnv ctx u = Env (map (map ($ metaEnv)) ctx) u

public export
ITerm : Syntax s ->
        (metaVars : Context Type) ->
        IContext metaVars s ->
        ISort metaVars s -> Type
ITerm syn metaVars vars a = (metaEnv : Env metaVars id) -> Term syn (map (map ($ metaEnv)) vars) (a metaEnv)

||| An axiom schema for a syntax
|||
||| For example, left identity:
|||   forall x : n. e * x = x
public export
record Axiom (syn : Syntax s) where
    constructor MkAxiom
    0 name : String
    metaVars : Context Type
    vars : IContext metaVars s
    {0 lhsSort : ISort metaVars s}
    lhs : ITerm syn metaVars vars lhsSort
    {0 rhsSort : ISort metaVars s}
    rhs : ITerm syn metaVars vars rhsSort

%name Axiom ax

||| A theory for a syntax
|||
||| For example, the laws of sized monoid theory:
||| - forall x : n. e * x = x
||| - forall x : n. x * e = x
||| - forall x : n, y : m, z : p. x * (y * z) = (x * y) * z
public export
data Theory : Syntax s -> Type where
    Lin : Theory syn
    (:<) : Theory syn -> Axiom syn -> Theory syn

%name Theory thy
