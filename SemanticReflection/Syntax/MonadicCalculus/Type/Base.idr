module Syntax.MonadicCalculus.Type.Base

%default total

public export
data Ty : t -> Type where
    Base : t -> Ty t
    Unit : Ty t
    Pair : Ty t -> Ty t -> Ty t
    T : Ty t -> Ty t

%name Ty a, b
