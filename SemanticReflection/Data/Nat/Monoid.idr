module Data.Nat.Monoid

import Data.Nat

import public Language.Monoid

%default total

%language ElabReflection

public export
[Additive] Model MonoidThy Nat where
    int = MkInterp `(\case
        e => 0
        (*) => (+)
    )

    satThy = [<
        Prf plusAssociative,
        Prf plusZeroLeftNeutral,
        Prf plusZeroRightNeutral
    ]

public export
[Multiplicative] Model MonoidThy Nat where
    int = MkInterp `(\case
        e => 1
        (*) => Prelude.(*)
    )

    satThy = [<
        Prf multAssociative,
        Prf plusZeroRightNeutral,
        Prf multOneRightNeutral
    ]
