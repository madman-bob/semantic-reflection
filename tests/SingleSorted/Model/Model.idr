import Data.List
import Data.Nat

import Syntax.SingleSorted.Model

%default total

%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)

MonoidThy : Theory MonoidSyn
MonoidThy = `([<
    x * (y * z) = (x * y) * z,
    e * x = x,
    x * e = x
  ])

Model MonoidThy (List a) where
    int = MkInterp `(\case
        e => []
        (*) => (++)
    )

    satThy = [<
        Prf appendAssociative,
        Prf \xs => Refl,
        Prf appendNilRightNeutral
    ]

Model MonoidThy Nat where
    int = MkInterp `(\case
        e => 0
        (*) => (+)
    )

    satThy = [<
        Prf plusAssociative,
        Prf plusZeroLeftNeutral,
        Prf plusZeroRightNeutral
    ]

eg : Term MonoidSyn [<"x", "y"]
eg = `(x * y)

listAssoc : (x : List a) ->
            (y : List a) ->
            (z : List a) ->
            x ++ (y ++ z) = (x ++ y) ++ z
listAssoc = getPrf {a = List a} $ There (There Here)
