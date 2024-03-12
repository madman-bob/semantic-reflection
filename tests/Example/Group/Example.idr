import Data.Bool.Group

%default total

%language ElabReflection

eg : Term GroupSyn [<"x", "y"]
eg = `(x * inv y)

boolEnv : Env [<"x", "y"] Bool
boolEnv = [<False, True]
