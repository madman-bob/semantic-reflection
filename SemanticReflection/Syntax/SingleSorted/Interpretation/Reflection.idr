module Syntax.SingleSorted.Interpretation.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Interpretation.Base
import public Syntax.SingleSorted.Syntax

%default total

export
opCase : {syn : Syntax} ->
         {0 p : Op syn -> Type} ->
         TTImp ->
         Elab ((op : Op syn) -> p op)
opCase (ILam fc MW ExplicitArg mn arg $ ICase fc' opts t ty clauses) = check $ ILam fc MW ExplicitArg mn arg $ ICase fc' opts t ty !(
    for clauses $ \case
        PatClause fc lhs rhs => pure $ PatClause fc !(quote !(operation {syn} lhs)) rhs
        clause => failAt fc "Expected operator case block with pattern clauses")
opCase h@(IHole _ _) = check h
opCase s = failAt (getFC s) "Expected operator case block"

%macro
export
fromTTImp : {syn : Syntax} ->
            {0 p : Op syn -> Type} ->
            TTImp ->
            Elab ((op : Op syn) -> p op)
fromTTImp s = opCase s

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
            IClaim fc MW Public [Totality Total] (MkTy fc fc opNm `({0 a : Type} -> Interp ~(IVar fc synNm) a => ~(Fun op.arity `(a) `(a)))),
            IDef fc opNm [PatClause fc (IVar fc opNm) `(impl {a} ~(!(quote op)))]
        ]
  where
    ||| Using this over standard Fun for better unification
    Fun : Nat -> TTImp -> TTImp -> TTImp
    Fun 0 a r = r
    Fun (S n) a r = `(~(a) -> ~(Fun n a r))
