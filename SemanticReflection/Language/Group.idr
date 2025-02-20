module Language.Group

import public Syntax.SingleSorted

%default total

%language ElabReflection

%hide Prelude.(*)

||| Group syntax
|||
||| A group has
||| - an associative binary operation
||| - an identity element
||| - a unary inverse operation
public export
GroupSyn : Syntax
GroupSyn = `[e : 0; (*) : 2; inv : 1]

||| Group theory
|||
||| A group has
||| - an associative binary operation
||| - an identity element
||| - a unary inverse operation
public export
GroupThy : Theory GroupSyn
GroupThy = `[
    assoc : x * (y * z) = (x * y) * z
    leftId : e * x = x
    rightId : x * e = x
    leftInv : inv x * x = e
    rightInv : x * inv x = e
  ]

%runElab openSyn `{GroupSyn}
%runElab openThy `{GroupThy}
