import Data.Nat

import Syntax.ManySorted.Env

%default total

%language ElabReflection

SomeCtx : Context Nat
SomeCtx = [<"x" :! 1, "y" :! 2]

SomeCtx' : Context Nat
SomeCtx' = `[x : 1; y : 2]

someCtxsEq : SomeCtx = SomeCtx'
someCtxsEq = Refl

failing "Mismatch between: Nat and String"
    badCtx : Context String
    badCtx = `[x : the Nat 1]

failing "Expected variable declaration"
    badCtx : Context Nat
    badCtx = `[x = 1]

someEnv : Env SomeCtx (`LT` 3)
someEnv = [<
    LTESucc (LTESucc LTEZero),
    LTESucc (LTESucc (LTESucc LTEZero))
  ]

anotherEnv : Env SomeCtx (`LT` 4)
anotherEnv = map lteSuccRight someEnv
