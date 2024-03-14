import Data.Bool.Group
import Data.List.Monoid
import Data.Vect.Pointwise

%default total

%language ElabReflection

monoidTerm : Term MonoidSyn [<"x", "y"]
monoidTerm = `(x * y)

groupTerm : Term GroupSyn [<"x", "y"]
groupTerm = `(x * inv y)

boolVectEnv : Env [<"x", "y"] (Vect 2 Bool)
boolVectEnv = [<[False, False], [False, True]]

listVectEnv : Env [<"x", "y"] (Vect 3 (List Nat))
listVectEnv = [<[[1, 2], [10], [13, 14]], [[3, 4], [11, 12], [15]]]

eg : Vect 3 (List Nat)
eg = evalEnv {thy = MonoidThy} listVectEnv monoidTerm

-- Check Pointwise evaluates at type-level
egCorrect : Main.eg = [[1, 2, 3, 4], [10, 11, 12], [13, 14, 15]]
egCorrect = Refl
