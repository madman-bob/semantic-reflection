module Syntax.ManySorted.Interpretation.Base

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Syntax

%default total

public export
anonCtx : List (Env i Prelude.id -> s) ->
          Env i Prelude.id ->
          Context s
anonCtx xs i = cast $ map (\a => ("", a i)) xs

||| An interpretation of a syntax, for a type universe
|||
||| This is given by an implementation of each operation of the syntax, with
||| appropriate signatures.
|||
||| Note that while operation indices must be respected, we do not require the
||| implementations to satisfy any further laws.
|||
||| For example, in the syntax of sized monoids, we could take
||| - `BoundInt n`, the integers of modulus at most n, as our sorts
||| - `0 : BoundInt 0`, as our identity
||| - subtraction as our binary operation
|||
||| This example satisfies the indexing requirement by the triangle inequality.
||| So this is an interpretation of sized monoid syntax, even though subtraction is
||| not associative.
public export
interface Interp (0 syn : Syntax s) (0 u : s -> Type) where
    constructor MkInterp
    impl : (op : Op syn) ->
           (i : Env op.index Prelude.id) ->
           Env (anonCtx op.arity i) u ->
           u (op.result i)

%name Interp int
