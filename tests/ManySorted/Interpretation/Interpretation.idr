import Data.Singleton
import Data.Vect

import Syntax.ManySorted.Interpretation

%default total

%language ElabReflection

||| Syntax of sized involutive monoids
SizedInvMonoidSyn : Syntax Nat
SizedInvMonoidSyn = `[
    e : 0
    inv : n -> n
    (*) : n -> m -> n + m
  ]

%runElab openSyn `{SizedInvMonoidSyn}

Interp SizedInvMonoidSyn Singleton where
    impl (MkOp (There (There Here))) [<] [<] = Val 0
    impl (MkOp (There Here)) [<n] [<x] = x
    impl (MkOp Here) [<n, m] [<x, y] = [| x + y |]

[Vec] Interp SizedInvMonoidSyn (\n => Vect n a) where
    impl = `(\case
        e => []
        inv x => reverse x
        xs * ys => xs ++ ys
      )
