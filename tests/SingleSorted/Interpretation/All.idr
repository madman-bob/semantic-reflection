import Data.DPair
import Data.Nat

import Syntax.SingleSorted.Interpretation.Env.All

%default total

SomeCtx : Context
SomeCtx = [<"x", "y", "z"]

SomeEnv : Env SomeCtx Nat
SomeEnv = [<1, 2, 3]

someEnvNonZero : All SomeEnv NonZero
someEnvNonZero = [<ItIsSucc, ItIsSucc, ItIsSucc]

twoNonZero : NonZero 2
twoNonZero = getAll someEnvNonZero (There Here)

someEnvGTZero : All SomeEnv (`GT` 0)
someEnvGTZero = mapAll {p = NonZero} {q = (`GT` 0)} (\ItIsSucc => LTESucc LTEZero) someEnvNonZero

SomeVars : SnocList (Exists $ \nm => Elem nm SomeCtx)
SomeVars = [<
    Evidence "z" Here,
    Evidence "x" (There (There Here)),
    Evidence "y" (There Here)
  ]

someVarsCovers : AllVars SomeCtx (\idx => Elem (Evidence _ idx) SomeVars)
someVarsCovers = [<
    There Here,
    Here,
    There (There Here)
  ]

someVarsCovers' : AllVars SomeCtx (\idx => Elem (Evidence _ idx) SomeVars)
someVarsCovers' = allVars $ \case
    Here => There (There Here)
    There Here => Here
    There (There Here) => There Here

someVarsCoversEq : Main.someVarsCovers = Main.someVarsCovers'
someVarsCoversEq = Refl

someEnvGTZero' : All SomeEnv (`GT` 0)
someEnvGTZero' = allVars' SomeEnv $ \case
    Here => LTESucc LTEZero
    There Here => LTESucc LTEZero
    There (There Here) => LTESucc LTEZero

someEnvGTZeroEq : Main.someEnvGTZero = Main.someEnvGTZero'
someEnvGTZeroEq = Refl

extendedVarsCovers : AllVars SomeCtx (\idx => Elem (Evidence _ idx) (moreVars ++ SomeVars))
extendedVarsCovers = mapAllVars elemRight someVarsCovers
  where
    elemRight : Elem x xs -> Elem x (ys ++ xs)
    elemRight Here = Here
    elemRight (There idx) = There (elemRight idx)
