import Syntax.STLC.Type

%default total

ctx : Context (Ty Nat)
ctx = [<
    "x" :! Base 1,
    "f" :! Base 1 ~> Base 2,
    "map1" :! (Base 1 ~> Base 2) ~> Base 3 ~> Base 4, -- Check precedence of (~>)
    "map2" :! (Base 2 ~> Base 4) ~> (Base 6 ~> Base 8) -- Check precedence of elaboration
  ]

ctx' : Context (Ty Nat)
ctx' = `[
    x : 1
    f : 1 -> 2
    map1 : (1 -> 2) -> 3 -> 4
    map2 : (2 -> 4) -> 6 -> 8
  ]

ctxsEq : Main.ctx = Main.ctx'
ctxsEq = Refl
