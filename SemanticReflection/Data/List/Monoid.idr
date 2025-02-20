module Data.List.Monoid

import Data.List

import public Language.Monoid

%default total

%language ElabReflection

public export
Model MonoidThy (List a) where
    int = `[
        e = []
        (*) = (++)
    ]

    satThy = [<
        Prf appendAssociative,
        Prf $ \xs => Refl,
        Prf appendNilRightNeutral
    ]
