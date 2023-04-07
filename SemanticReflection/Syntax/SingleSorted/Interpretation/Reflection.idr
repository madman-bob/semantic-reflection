module Syntax.SingleSorted.Interpretation.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Syntax

%default total

export
opCase : {syn : Syntax} ->
         {0 p : Op syn -> Type} ->
         TTImp ->
         Elab ((op : Op syn) -> p op)
opCase (ILam fc MW ExplicitArg mn arg $ ICase fc' t ty clauses) = check $ ILam fc MW ExplicitArg mn arg $ ICase fc' t ty !(
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
