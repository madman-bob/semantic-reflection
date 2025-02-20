module Syntax.SingleSorted.Interpretation.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Interpretation.Base
import public Syntax.SingleSorted.Syntax

%default total

export
opCase : Syntax ->
         List Decl ->
         Elab TTImp
opCase syn decls = do
    clauses <- traverse case_ decls
    lcase <- genSym "lcase"
    pure $ ILam EmptyFC MW ExplicitArg (Just lcase) (Implicit EmptyFC False)
        (ICase EmptyFC [] (IVar EmptyFC lcase) (Implicit EmptyFC False) clauses)
  where
    lookupOp' : FC -> String -> SnocList RawOp -> TTImp -> Elab TTImp
    lookupOp' fc nm [<] acc = failAt fc "Operator not in syntax"
    lookupOp' fc nm (rawOps :< rawOp) acc = if rawOp.name == nm
        then pure `(MkOp ~(acc))
        else lookupOp' fc nm rawOps `(There ~(acc))

    lookupOp : FC -> String -> Elab TTImp
    lookupOp fc nm = lookupOp' fc nm syn.rawOps `(Here)

    case_ : Decl -> Elab Clause
    case_ (IDef _ _ [PatClause _ (IVar fc (UN (Basic nm))) rhs]) = do
        op <- lookupOp fc nm
        pure $ PatClause fc op rhs
    case_ decl = fail "Expected operator definition"

namespace OpCase
    %macro
    export
    fromDecls : {syn : Syntax} ->
                {0 p : Op syn -> Type} ->
                List Decl ->
                Elab ((op : Op syn) -> p op)
    fromDecls decls = check !(opCase syn decls)

%macro
export
fromDecls : {syn : Syntax} ->
            List Decl ->
            Elab (Interp syn a)
fromDecls decls = check `(MkInterp ~(!(opCase syn decls)))

||| Open a syntax in the current namespace
|||
||| This creates Idris-level equivalents of the operators in the syntax.
|||
||| For example, in the syntax of monoids, we already have the operators
||| - `(e) : Op MonoidSyn
||| - `((*)) : Op MonoidSyn
|||
||| This script creates Idris-level names for interpretations of these operators.
||| - e : Interp MonoidSyn a => a
||| - (*) : Interp MonoidSyn a => a -> a -> a
export
openSyn : (synNm : Name) -> Elab ()
openSyn synNm = do
    let fc = EmptyFC
    syn <- check $ IVar fc synNm
    for_ syn.ops $ \op => do
        let opNm = UN $ Basic op.name
        declare [
            IClaim $ MkFCVal fc $ MkIClaimData MW Public [Totality Total] (MkTy fc (MkFCVal fc opNm) `({0 a : Type} -> Interp ~(IVar fc synNm) a => ~(Fun op.arity `(a) `(a)))),
            IDef fc opNm [PatClause fc (IVar fc opNm) `(impl {a} ~(!(quote op)))]
        ]
  where
    ||| Using this over standard Fun for better unification
    Fun : Nat -> TTImp -> TTImp -> TTImp
    Fun 0 a r = r
    Fun (S n) a r = `(~(a) -> ~(Fun n a r))
