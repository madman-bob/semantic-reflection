import Syntax.SingleSorted.Interpretation

%default total

SomeCtx : Context
SomeCtx = [<"x", "y", "z"]

intEnv : Env SomeCtx Integer
intEnv = [<1, 2, 3]

stringEnv : Env SomeCtx String
stringEnv = [<"Hello ", "world", "!"]

failing #"Mismatch between: [<] and [<"x", "y", "z"]."#
    badEnv : Env SomeCtx Integer
    badEnv = [<]

intFun : Env SomeCtx Integer -> Integer
intFun [<x, y, z] = x - y

stringFun : Fun SomeCtx String
stringFun x y z = x ++ y ++ z

%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)

%runElab openSyn `{MonoidSyn}

Interp MonoidSyn Integer where
    impl (MkOp Here) = (-)
    impl (MkOp (There Here)) = 0

Interp MonoidSyn String where
    impl = `(\case e => ""; (*) => (++))

failing "Expected operator case block"
    [Bad] Interp MonoidSyn Integer where
        impl = `(0)

failing "Expected operator case block with pattern clauses"
    [Bad] Interp MonoidSyn String where
        impl = `(\case e => ""; (*) impossible)
