module Language.Monoid

import public Syntax.SingleSorted

%default total

%language ElabReflection

||| Monoid syntax
|||
||| A monoid has
||| - an associative binary operation
||| - an identity element
public export
MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)

||| Monoid theory
|||
||| A monoid has
||| - an associative binary operation
||| - an identity element
public export
MonoidThy : Theory MonoidSyn
MonoidThy = `([<
    x * (y * z) = (x * y) * z,
    e * x = x,
    x * e = x
  ])
