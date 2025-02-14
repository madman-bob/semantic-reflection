import Syntax.MonadicCalculus.Syntax

%default total

data BaseType = Loc | Bit

MemMan : Syntax BaseType
MemMan = MkSyntax [<
    "read" :! MkPrimitive (Base Loc) (T (Base Bit)),
    "write" :! MkPrimitive (Pair (Base Loc) (Base Bit)) (T Unit),
    "alloc" :! MkPrimitive (Base Bit) (T (Base Loc)),
    "true" :! MkPrimitive Unit (Base Bit),
    "false" :! MkPrimitive Unit (Base Bit)
  ]

MemMan' : Syntax BaseType
MemMan' = `[
    read : Loc -> T Bit
    write : (Loc, Bit) -> T ()
    alloc : Bit -> T Loc
    true : () -> Bit
    false : () -> Bit
  ]

MemMan'' : Syntax BaseType
MemMan'' = `[
    read : Loc -> T Bit
    write : Loc -> Bit -> T ()
    alloc : Bit -> T Loc
    true : Bit
    false : Bit
  ]

MemMansEq : (MemMan = MemMan', MemMan = MemMan'')
MemMansEq = (Refl, Refl)
