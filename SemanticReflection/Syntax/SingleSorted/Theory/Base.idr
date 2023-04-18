module Syntax.SingleSorted.Theory.Base

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term

%default total

||| An axiom for a syntax
|||
||| For simplicity, we are only considering equational axioms.
||| ie. equations of the form: forall x, y, ..., z. t1 = t2
|||
||| For example, in the syntax of monoids,
|||   forall x. e * x = x
||| is equational.
|||
||| While the field syntax axiom
|||   forall x. x != 0 => x * inv x = 1
||| is not equational, as it involves implication.
public export
record Axiom (syn : Syntax) where
    constructor MkAxiom
    0 vars : Context
    lhs : Term syn vars
    rhs : Term syn vars

%name Axiom ax

||| A theory for a syntax is additional relations between terms.
|||
||| For simplicity, we are only considering equational axioms.
||| ie. equations of the form: forall x, y, ..., z. t1 = t2
|||
||| For example, the monoid laws are
||| - forall x. e * x = x
||| - forall x. x * e = x
||| - forall x, y, z. x * (y * z) = (x * y) * z
public export
data Theory : Syntax -> Type where
    Lin : Theory syn
    (:<) : Theory syn -> Axiom syn -> Theory syn

%name Theory thy
