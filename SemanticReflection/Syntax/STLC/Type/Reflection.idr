module Syntax.STLC.Type.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Env

import public Syntax.STLC.Type.Base

%default total

export
stlcType : TTImp -> Elab TTImp
stlcType (IPi _ MW ExplicitArg Nothing a b) = do
    a <- stlcType a
    b <- stlcType b
    pure `(~(a) ~> ~(b))
stlcType i@(Implicit _ _) = pure i
stlcType h@(IHole _ _) = pure h
stlcType s = pure `(Base ~(s))

export
%macro
fromTTImp : TTImp -> Elab (Ty a)
fromTTImp t = check !(stlcType t)

export
stlcContext : List Decl -> Elab TTImp
stlcContext = contextBy stlcType """
    Expected variable declaration
    eg.
      someCtx : Context (Ty Nat)
      someCtx = `[f : 1 -> 2; x : 1]
    """

export
%macro
fromDecls : List Decl -> Elab (Context (Ty a))
fromDecls decls = check !(stlcContext decls)
