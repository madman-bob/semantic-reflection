import Syntax.MonadicCalculus.Type

%default total

ctx : Context (Ty Nat)
ctx = [<
    "x" :! Base 1,
    "y" :! Pair (Base 1) (Base 2),
    "z" :! T (Base 2),
    "big" :! T (Pair (Base 1) (T (Pair (Base 2) (Base 3))))
  ]

ctx' : Context (Ty Nat)
ctx' = `[
    x : 1
    y : (1, 2)
    z : T 2
    big : T (1, T (2, 3))
  ]

ctxsEq : Main.ctx = Main.ctx'
ctxsEq = Refl
