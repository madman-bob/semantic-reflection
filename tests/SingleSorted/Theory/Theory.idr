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
leftId = MkAxiom "leftId" [<"x"] `(e * x) `(x)

leftId' : Axiom MonoidSyn
leftId' = `[leftId : e * x = x]

leftIdsEq : Main.leftId = Main.leftId'
leftIdsEq = Refl

failing "Expected axiom"
    badAx : Axiom MonoidSyn
    badAx = `[leftId : e * x]

failing "Expected single axiom"
    badAx : Axiom MonoidSyn
    badAx = `[leftId : e * x = x; rightId : x * e = x]

MonoidThy : Theory MonoidSyn
MonoidThy = [<
    `[assoc : x * (y * z) = (x * y) * z],
    leftId,
    `[rightId : x * e = x]
  ]

MonoidThy' : Theory MonoidSyn
MonoidThy' = `[
    assoc : x * (y * z) = (x * y) * z
    leftId : e * x = x
    rightId : x * e = x
  ]

MonoidThysEq : MonoidThy = MonoidThy'
MonoidThysEq = Refl

[ConcatLeftId] SatAxiom ConcatInterp Main.leftId where
    prf x = Refl

ConcatSatMonoidThy : SatTheory ConcatInterp MonoidThy
ConcatSatMonoidThy = [<
    Prf appendAssociative,
    ConcatLeftId,
    Prf appendNilRightNeutral
  ]

ConcatRightId : SatAxiom ConcatInterp `[rightId : x * e = x]
ConcatRightId = getSatAxiom @{ConcatSatMonoidThy} Here
