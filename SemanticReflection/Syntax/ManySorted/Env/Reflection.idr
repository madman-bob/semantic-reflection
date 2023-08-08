module Syntax.ManySorted.Env.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Env.Base

%default total

namespace Context
    export
    context : List Decl -> Elab (Context s)
    context decls = context' $ cast decls
      where
        context' : SnocList Decl -> Elab (Context s)
        context' = traverse $ \case
            IClaim _ MW Private [] (MkTy _ _ (UN (Basic nm)) a) => [| pure nm :! check a |]
            _ => fail """
                Expected variable declaration
                eg.
                  someCtx : Context Nat
                  someCtx = `[x : 1; y : 2]
                """

    %macro
    export
    fromDecls : List Decl -> Elab (Context s)
    fromDecls decls = context decls
