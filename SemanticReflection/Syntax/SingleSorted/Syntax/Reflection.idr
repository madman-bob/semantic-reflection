module Syntax.SingleSorted.Syntax.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Syntax.Base

%default total

export
snocListLit : Foldable f =>
              f TTImp ->
              TTImp
snocListLit xs = foldl
    (\xs, x => IApp EmptyFC (IApp EmptyFC (IVar EmptyFC `{(:<)}) xs) x)
    (IVar EmptyFC `{Lin})
    xs

namespace Operation
    export
    opName : TTImp -> Elab String
    opName (IVar fc (UN (Basic nm))) = pure nm
    opName (IBindVar fc (UN (Basic nm))) = pure nm
    opName s = failAt (getFC s) "Expected operator"

    export
    operation : Syntax -> TTImp -> Elab TTImp
    operation syn s = do
        let fc = getFC s

        nm <- opName s
        let nm = IPrimVal fc $ Str nm
        let search = mapTopmostFC (const fc) `(%search)

        pure $ `(forgetName {nm = ~(nm)} ~(search))

    %macro
    export
    fromTTImp : {syn : Syntax} -> TTImp -> Elab (Op syn)
    fromTTImp s = check !(operation syn s)

export
rawOp : Decl -> Elab TTImp
rawOp (IClaim (MkFCVal _ (MkIClaimData MW Private [] (MkTy _ (MkFCVal fc (UN (Basic nm))) arity)))) = do
    let nm = IPrimVal fc $ Str nm
    pure `(MkRawOp ~(nm) ~(arity))
rawOp decl = fail "Expected operation declaration\neg. `[e = 0; (*) : 2; inv : 1]"

export
syntax : List Decl -> Elab TTImp
syntax decls = do
    rawOps <- traverse rawOp decls
    pure `(MkSyntax ~(snocListLit rawOps))

%macro
export
fromDecls : List Decl -> Elab Syntax
fromDecls decls = check !(syntax decls)
