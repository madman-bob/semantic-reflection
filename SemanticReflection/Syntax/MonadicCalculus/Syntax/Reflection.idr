module Syntax.MonadicCalculus.Syntax.Reflection

import public Language.Reflection

import public Syntax.MonadicCalculus.Syntax.Base

%default total

export
primitive : Decl -> Elab TTImp
primitive (IClaim (MkFCVal _ (MkIClaimData MW Private [] (MkTy _ (MkFCVal fc (UN (Basic nm))) tys)))) = do
    let nm = IPrimVal fc $ Str nm
    let (args, ret) = collectArgs tys [<]
    let args = prod !(traverse ty args)
    ret <- ty ret
    pure `(~(nm) :! MkPrimitive ~(args) ~(ret))
  where
    collectArgs : TTImp -> SnocList TTImp -> (List TTImp, TTImp)
    collectArgs (IPi _ MW ExplicitArg Nothing a b) ss = collectArgs b (ss :< a)
    collectArgs t ts = (cast ts, t)

    prod : List TTImp -> TTImp
    prod [] = `(Unit)
    prod [t] = t
    prod (t :: ts) = `(Pair ~(t) ~(prod ts))
primitive decl = fail "Language does not support this construct"

export
syntax : List Decl -> Elab TTImp
syntax decls = do
    prims <- traverse primitive decls
    pure `(MkSyntax ~(snocListLit prims))

export
%macro
fromDecls : List Decl -> Elab (Syntax t)
fromDecls decls = check !(syntax decls)
