import Language.Monoid.UnusedVar
import Decidable.Decidable

%language ElabReflection

x : Elem "x" [<"x", "y", "z"]
x = There (There Here)

y : Elem "y" [<"x", "y", "z"]
y = There Here

z : Elem "z" [<"x", "y", "z"]
z = Here

egSimple : Term MonoidSyn [<"x", "y", "z"]
egSimple = `(x)

egComplex : Term MonoidSyn [<"x", "y", "z"]
egComplex = `((x * z) * (x * x) * z)
