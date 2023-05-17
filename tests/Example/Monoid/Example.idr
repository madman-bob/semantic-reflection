import Data.Bool.Monoid
import Data.List.Monoid
import Data.Nat.Monoid

%default total

%language ElabReflection

eg : Term MonoidSyn [<"x", "y"]
eg = `(x * y)

natEnv : Env [<"x", "y"] Nat
natEnv = [<3, 2]

listEnv : Env [<"x", "y"] (List Nat)
listEnv = [<[1, 2], [3, 4]]

boolEnv : Env [<"x", "y"] Bool
boolEnv = [<False, True]
