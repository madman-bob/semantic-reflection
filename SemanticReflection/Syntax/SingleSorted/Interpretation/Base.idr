module Syntax.SingleSorted.Interpretation.Base

import public Syntax.SingleSorted.Interpretation.Env
import public Syntax.SingleSorted.Interpretation.Fun
import public Syntax.SingleSorted.Syntax

%default total

||| An interpretation of a syntax, for a type
|||
||| This is given by an implementation of each operation of the syntax, with
||| appropriate arities.
|||
||| Note that we do not require the implementations satisfy any laws.
|||
||| For example, in the syntax of monoids, we could take
||| - Integer as our collection of values
||| - 0 as our identity
||| - subtraction as our binary operation
||| This example does not satisfy the monoid laws, but is still an interpretation
public export
interface Interp (0 syn : Syntax) (0 a : Type) where
    constructor MkInterp
    impl : (op : Op syn) -> Fun (anonCtx op.arity) a

%name Interp int
