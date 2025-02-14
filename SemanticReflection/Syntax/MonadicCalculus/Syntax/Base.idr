module Syntax.MonadicCalculus.Syntax.Base

import public Syntax.ManySorted.Env

import public Syntax.MonadicCalculus.Type

%default total

public export
record Primitive (t : Type) where
    [noHints]
    constructor MkPrimitive
    arg : Ty t
    result : Ty t

public export
record Syntax (t : Type) where
    [noHints]
    constructor MkSyntax
    primitives : Context (Primitive t)
