module Syntax.ManySorted.Model.Equiv

import Control.Relation

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Model.Base
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term
import public Syntax.ManySorted.Theory

%default total

||| Semantic equivalence between two terms
|||
||| Two terms are semantically equivalent when they evaluate to the same value in
||| all models and environments.
public export
interface Equiv (0 thy : Theory {s} syn) (0 x : Term {s} syn ctx a) (0 y : Term {s} syn ctx b) where
    constructor IsEquiv
    isEquiv : forall u.
              Model thy u =>
              (env : Env ctx u) ->
              eval env x ~=~ eval env y

public export
Reflexive (Term syn ctx a) (Equiv thy) where
    reflexive = IsEquiv (\env => Refl)

public export
Symmetric (Term syn ctx a) (Equiv thy) where
    symmetric (IsEquiv xy) = IsEquiv (\env => sym $ xy env)

public export
Transitive (Term syn ctx a) (Equiv thy) where
    transitive (IsEquiv xy) (IsEquiv yz) = IsEquiv (\env => trans (xy env) (yz env))

public export
Euclidean (Term syn ctx a) (Equiv thy) where
    euclidean = euclidean @{TSE}

public export
Tolerance (Term syn ctx a) (Equiv thy) where

public export
PartialEquivalence (Term syn ctx a) (Equiv thy) where

public export
Equivalence (Term syn ctx a) (Equiv thy) where
