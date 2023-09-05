module Syntax.SingleSorted.Syntax.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Syntax.Base

%default total

namespace Operation
    export
    opName : TTImp -> Elab String
    opName (IVar fc (UN (Basic nm))) = pure nm
    opName (IBindVar fc nm) = pure nm
    opName s = failAt (getFC s) "Expected operator"

    export
    operation : {syn : Syntax} -> TTImp -> Elab (Op syn)
    operation s = do
        nm <- opName s
        let Just op = findOp nm
            | Nothing => failAt (getFC s) "Operator \{show nm} not in syntax \{show syn}"
        pure op

    %macro
    export
    fromTTImp : {syn : Syntax} -> TTImp -> Elab (Op syn)
    fromTTImp s = operation s

export
syntax : TTImp -> Elab Syntax
syntax (ILam fc MW ExplicitArg _ _ $ ICase _ [] _ _ clauses) = do
    ops <- traverse rawOp $ clauses
    pure $ MkSyntax $ cast ops
  where
    rawOp : Clause -> Elab RawOp
    rawOp (PatClause _ lhs rhs) = [| MkRawOp (opName lhs) (check rhs) |]
    rawOp clause = failAt fc "Expected pattern clause"
syntax s = failAt (getFC s) "Expected signature using \\case block\neg. `(\\case e => 0; (*) => 2; inv => 1)"

%macro
export
fromTTImp : TTImp -> Elab Syntax
fromTTImp s = syntax s
