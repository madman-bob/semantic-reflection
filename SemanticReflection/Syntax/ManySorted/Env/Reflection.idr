module Syntax.ManySorted.Env.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Env.Base

%default total

export
snocListLit : Foldable f =>
              f TTImp ->
              TTImp
snocListLit xs = foldl
    (\xs, x => IApp EmptyFC (IApp EmptyFC (IVar EmptyFC `{(:<)}) xs) x)
    (IVar EmptyFC `{Lin})
    xs

namespace Context
    export
    contextBy : (TTImp -> Elab TTImp) ->
                (failMsg : String) ->
                List Decl ->
                Elab TTImp
    contextBy f failMsg decls = map snocListLit $ for decls $ \case
        IClaim (MkFCVal _ $ MkIClaimData MW Private [] (MkTy _ (MkFCVal fc $ UN (Basic nm)) a)) => do
            let nm = IPrimVal fc $ Str nm
            a <- f a
            pure `(~(nm) :! ~(a))
        _ => fail failMsg

    export
    context : List Decl -> Elab TTImp
    context = contextBy pure """
        Expected variable declaration
        eg.
          someCtx : Context Nat
          someCtx = `[x : 1; y : 2]
        """

    %macro
    export
    fromDecls : List Decl -> Elab (Context s)
    fromDecls decls = check !(context decls)
