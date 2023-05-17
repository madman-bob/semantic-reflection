module Data.Bool.Monoid

import Data.Bool
import Data.Bool.Xor

import public Language.Monoid

%default total

%language ElabReflection

public export
[And] Model MonoidThy Bool where
    int = MkInterp `(\case
        e => True
        (*) => \x, y => x && y
    )

    satThy = [<
        Prf andAssociative,
        Prf $ \x => Refl,
        Prf andTrueNeutral
    ]

public export
[Or] Model MonoidThy Bool where
    int = MkInterp `(\case
        e => False
        (*) => \x, y => x || y
    )

    satThy = [<
        Prf orAssociative,
        Prf $ \x => Refl,
        Prf orFalseNeutral
    ]

public export
[Xor] Model MonoidThy Bool where
    int = MkInterp `(\case
        e => False
        (*) => xor
    )

    satThy = [<
        Prf xorAssociative,
        Prf xorFalseNeutral,
        Prf $ \x => trans (xorCommutative x False) $ xorFalseNeutral x
    ]
