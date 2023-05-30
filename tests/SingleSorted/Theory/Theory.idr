import Data.List

import Syntax.SingleSorted.Theory

%default total

%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)

[ConcatInterp] Interp MonoidSyn (List a) where
    impl = `(\case
        e => []
        (*) => (++)
    )

leftId : Axiom MonoidSyn
leftId = MkAxiom [<"x"] `(e * x) `(x)

leftId' : Axiom MonoidSyn
leftId' = `(e * x = x)

leftIdsEq : Main.leftId = Main.leftId'
leftIdsEq = Refl

failing "Expected axiom"
    badAx : Axiom MonoidSyn
    badAx = `(e * x)

MonoidThy : Theory MonoidSyn
MonoidThy = [<
    `(x * (y * z) = (x * y) * z),
    leftId,
    `(x * e = x)
  ]

MonoidThy' : Theory MonoidSyn
MonoidThy' = `([<
    x * (y * z) = (x * y) * z,
    e * x = x,
    x * e = x
  ])

MonoidThysEq : MonoidThy = MonoidThy'
MonoidThysEq = Refl

failing "Expected theory"
    badThy : Theory MonoidSyn
    badThy = `(e * x = x)

[ConcatLeftId] SatAxiom ConcatInterp Main.leftId where
    prf x = Refl

ConcatSatMonoidThy : SatTheory ConcatInterp MonoidThy
ConcatSatMonoidThy = [<
    Prf appendAssociative,
    ConcatLeftId,
    Prf appendNilRightNeutral
  ]

ConcatRightId : SatAxiom ConcatInterp `(x * e = x)
ConcatRightId = getSatAxiom @{ConcatSatMonoidThy} Here
