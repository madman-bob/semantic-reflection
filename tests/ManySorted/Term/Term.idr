import Data.Singleton
import Data.Vect

import Syntax.ManySorted.Term

%default total

%language ElabReflection

SizedInvMonoidSyn : Syntax Nat
SizedInvMonoidSyn = `[
    e : 0
    inv : n -> n
    (*) : n -> m -> n + m
]

eg : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
eg = Operation `((*)) [<_, _] [<
    Operation `((*)) [<_, _] [<
        Var $ There Here,
        Operation `(e) [<] [<]
    ],
    Operation `(inv) [<_] [<
        Var Here
    ]
]

eg' : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
eg' = `((x * e) * inv y)

egsEq : Main.eg = Main.eg'
egsEq = Refl

eg2 : Term SizedInvMonoidSyn `[x : 1; y : 2; z : 3] 8
eg2 = `(y * (x * z) * y)

eg3 : Term SizedInvMonoidSyn `[x : 1; y : 2] 2
eg3 = `(x * ?someHole)

failing #"Can't find an implementation for NVar [<("x", 1), ("y" :! 2)] "z" 3."#
    badEg : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
    badEg = `(z)

failing #"Operation "f" not in syntax"#
    badEg : Term SizedInvMonoidSyn `[f : 1; x : 2] 3
    badEg = `(f x)

failing #"Operation "f" not in syntax"#
    badEg : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
    badEg = `(f x)

failing #"Operation "*" has arity 2, given 0 arg(s)"#
    badEg : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
    badEg = `((*))

failing #"Operation "e" has arity 0, given 1 arg(s)"#
    badEg : Term SizedInvMonoidSyn `[x : 1; y : 2] 3
    badEg = `(e x)

Interp SizedInvMonoidSyn Singleton where
    impl = `[
        e = Val 0
        inv x = x
        x * y = [| x + y |]
    ]

[Vec] Interp SizedInvMonoidSyn (\n => Vect n a) where
    impl = `[
        e = []
        inv x = reverse x
        x * y = x ++ y
    ]

[ShowInterp] Interp SizedInvMonoidSyn (const String) where
    impl = `[
        e = "e"
        inv x = "(inv \{x})"
        x * y = "(\{x} * \{y})"
    ]

{ctx : Context Nat} -> Show (Term SizedInvMonoidSyn ctx a) where
    show x = unsafeEval @{ShowInterp} (names ctx) x
      where
        names : (c : Context s) -> Env c (const String)
        names [<] = [<]
        names (c :< (nm, a)) = names c :< nm

termEnv : Env `[x : 1; y : 2; z : 3] (Term SizedInvMonoidSyn `[a : 1; b : 2])
termEnv = [<`(a), `(b), `(a * b)]
