module Data.Bool.Group

import Data.Bool.Xor

import Syntax.PreorderReasoning

import public Language.Group

%default total

%language ElabReflection

public export
[Xor] Model GroupThy Bool where
    int = MkInterp `(\case
        e => False
        (*) => xor
        inv => id
    )

    satThy = [<
        Prf xorAssociative,
        Prf xorFalseNeutral,
        Prf xorFalseNeutralRight,
        Prf xorSameFalse,
        Prf xorSameFalse
    ]
      where
        xorFalseNeutralRight : (x : Bool) -> x `xor` False = x
        xorFalseNeutralRight x = Calc $
            |~ x `xor` False
            ~~ False `xor` x    ...(xorCommutative x False)
            ~~ x                ...(xorFalseNeutral x)
