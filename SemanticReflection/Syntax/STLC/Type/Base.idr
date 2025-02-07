module Syntax.STLC.Type.Base

%default total

export infixr 1 ~>

public export
data Ty : t -> Type where
    Base : t -> Ty t
    (~>) : Ty t -> Ty t -> Ty t

%name Ty a, b
