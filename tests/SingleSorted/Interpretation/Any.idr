import Data.Nat

import Syntax.SingleSorted.Interpretation.Env.Any

%default total

SomeCtx : Context
SomeCtx = [<"x", "y", "z"]

SomeEnv : Env SomeCtx Nat
SomeEnv = [<1, 2, 3]

someEnvHasGTOne : Any SomeEnv (`GT` 1)
someEnvHasGTOne = There (Here (LTESucc (LTESucc LTEZero)))

someIdxGTOne : Exists $ \nm => (idx : Elem nm SomeCtx ** get SomeEnv idx `GT` 1)
someIdxGTOne = getAny someEnvHasGTOne

SomeVar : Exists $ \nm => Elem nm SomeCtx
SomeVar = Evidence "y" (There Here)

someVarPresent : AnyVar SomeCtx (\idx => Evidence _ idx = SomeVar)
someVarPresent = There (Here Refl)
