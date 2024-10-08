import Data.Nat
import Data.Singleton

import Syntax.ManySorted.Model

%default total

%language ElabReflection

SizedMonoidSyn : Syntax Nat
SizedMonoidSyn = `[
    e : 0
    (*) : n -> m -> n + m
  ]

SizedMonoidThy : Theory SizedMonoidSyn
SizedMonoidThy = `[
    leftId : {x : n} -> e * x = x
    rightId : {x : n} -> x * e = x
    assoc : {x : n} -> {y : m} -> {z : p} -> x * (y * z) = (x * y) * z
  ]

%runElab openSyn `{SizedMonoidSyn}
%runElab openThy `{SizedMonoidThy}
%hide Prelude.(*)

Model SizedMonoidThy (Singleton {a = Nat}) where
    int = MkInterp `(\case
        e => Val 0
        x * y => [| x + y |]
    )

    satThy = [<
        MkSatAxiom $ \[<n], [<Val n] => Refl,
        MkSatAxiom $ \[<n], [<Val n] => rewrite plusZeroRightNeutral n in Refl,
        MkSatAxiom $ \[<n, m, p], [<Val n, Val m, Val p] => rewrite plusAssociative n m p in Refl
    ]

eg : Term SizedMonoidSyn `[x : 1; y : 2] 3
eg = `(x * y)

someEquiv : Equiv SizedMonoidThy `((e * x) * (y * e)) Main.eg
someEquiv = IsEquiv $ \[<x, y] => cong2 (*) (leftId x) (rightId y)

nxe : Not (Equiv SizedMonoidThy Main.eg `(e))
nxe (IsEquiv isEquiv) = case isEquiv {u = Singleton} [<Val 1, Val 2] of Refl impossible
