import Syntax.SingleSorted.Interpretation

%default total

SomeCtx : Context
SomeCtx = [<"x", "y", "z"]

intEnv : Env SomeCtx Integer
intEnv = [<1, 2, 3]

stringEnv : Env SomeCtx String
stringEnv = [<"Hello ", "world", "!"]

tupleEnv : Env SomeCtx (Bool, Nat, String)
tupleEnv = [<(False, 0, "Lorem"), (True, 1, "ipsum"), (False, 2, "dolor")]

failing #"Mismatch between: [<] and [<"x", "y", "z"]."#
    badEnv : Env SomeCtx Integer
    badEnv = [<]

intFun : Env SomeCtx Integer -> Integer
intFun [<x, y, z] = x - y

stringFun : Fun SomeCtx String
stringFun x y z = x ++ y ++ z

%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `[e : 0; (*) : 2]

%runElab openSyn `{MonoidSyn}

Interp MonoidSyn Integer where
    impl (MkOp Here) = (-)
    impl (MkOp (There Here)) = 0

Interp MonoidSyn String where
    impl = `[e = ""; (*) = (++)]

failing "Expected operator definition"
    [Bad] Interp MonoidSyn Integer where
        impl = `[e : 0]

failing "Expected operator definition"
    [Bad] Interp MonoidSyn String where
        impl = `[e = ""; (*) impossible]
