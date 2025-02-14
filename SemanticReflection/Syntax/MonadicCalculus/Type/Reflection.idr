module Syntax.MonadicCalculus.Type.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Env

import public Syntax.MonadicCalculus.Type.Base

%default total

export
ty : TTImp -> Elab TTImp
ty `(()) = pure `(Unit)
ty (IAlternative _ (UniqueDefault `(~(IVar _ `{Builtin.MkPair}) ~(x) ~(y))) _) = do
    x <- ty x
    y <- ty y
    pure `(Pair ~(x) ~(y))
ty `(T ~(x)) = do
    x <- ty x
    pure `(T ~(x))
ty t = pure `(Base ~(t))

export
%macro
fromTTImp : TTImp -> Elab (Ty t)
fromTTImp t = check !(ty t)

export
tyContext : List Decl -> Elab TTImp
tyContext = contextBy ty """
    Expected variable declaration
    eg.
      someCtx : Context (Ty Nat)
      someCtx = `[x : 1; y : (2, 3); z : T 4]
    """

export
%macro
fromDecls : List Decl -> Elab (Context (Ty t))
fromDecls decls = check !(tyContext decls)
