import Syntax.ManySorted.Syntax

%default total

%language ElabReflection

e : RawOp Nat
e = MkRawOp
    {name = "e"}
    {index = [<]}
    {arity = []}
    {result = const 0}

SizedMonoidSyn : Syntax Nat
SizedMonoidSyn = MkSyntax [<
    e,
    `[(*) : n -> m -> n + m]
  ]

failing "Expected operator declaration"
    badRawOp : RawOp Nat
    badRawOp = `[e = 0]

failing "Expected single operator declaration"
    badRawOp : RawOp Nat
    badRawOp = `[
        e : 0
        (*) : n -> m -> n + m
      ]

concat : Op SizedMonoidSyn
concat = MkOp Here

data ModuleSort = Matrix Nat Nat | Vector Nat

ModuleSyn : Syntax ModuleSort
ModuleSyn = `[
    I : Matrix n n
    (<+>) : Matrix n m -> Matrix n m -> Matrix n m
    (<*>) : Matrix n m -> Matrix m p -> Matrix n p
    (+) : Vector n -> Vector n -> Vector n
    (*) : Matrix n m -> Vector m -> Vector n
  ]

failing "Expected operator declaration"
    badSyn : Syntax ModuleSort
    badSyn = `[
        I = Matrix n n
      ]

moduleVectAdd : Op ModuleSyn
moduleVectAdd = `((+))

failing #"Operator "e" not in syntax"#
    badOp : Op ModuleSyn
    badOp = `(e)
