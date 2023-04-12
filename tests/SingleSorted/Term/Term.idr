import Syntax.SingleSorted.Term

%default total

%language ElabReflection

GroupSyn : Syntax
GroupSyn = `(\case e => 0; (*) => 2; inv => 1)

eg : Term GroupSyn [<"x", "y"]
eg = Operation `((*)) [<
    Operation `((*)) [<
        Var $ There Here,
        Operation `(e) [<]
    ],
    Operation `(inv) [<
        Var Here
    ]
]

eg' : Term GroupSyn [<"x", "y"]
eg' = `(x * e * inv y)

egsEq : Main.eg = Main.eg'
egsEq = Refl

eg2 : Term GroupSyn [<"x", "y", "z"]
eg2 = `(y * (x * z) * x)

failing #"Variable "z" not in context [< "x", "y"]"#
    badEg : Term GroupSyn [<"x", "y"]
    badEg = `(z)

failing #"Variable "f" is not a function"#
    badEg : Term GroupSyn [<"f", "x"]
    badEg = `(f x)

Interp GroupSyn String where
    impl = `(\case
        e => "e"
        (*) => \x, y => "(\{x} * \{y})"
        inv => \x => "(inv \{x})"
    )

{ctx : Context} -> Show (Term GroupSyn ctx) where
    show x = unsafeEvalEnv (names ctx) x
      where
        names : (c : Context) -> Env c String
        names [<] = [<]
        names (c :< nm) = names c :< nm

Interp GroupSyn Integer where
    impl = `(\case e => 0; (*) => (-); inv => (+ 1))
