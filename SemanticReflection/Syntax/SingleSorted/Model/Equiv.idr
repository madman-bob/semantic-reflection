module Syntax.SingleSorted.Model.Equiv

import Control.Relation

import public Syntax.SingleSorted.Model.Base
import public Syntax.SingleSorted.Term
import public Syntax.SingleSorted.Theory

%default total

||| Semantic equivalence between two terms
|||
||| Two terms are semantically equivalent when they evaluate to the same value in
||| all models and environments.
public export
interface Equiv (0 thy : Theory syn) (0 x : Term syn ctx) (0 y : Term syn ctx) where
    constructor IsEquiv
    isEquiv : forall a.
              Model thy a =>
              (env : Env ctx a) ->
              evalEnv env x = evalEnv env y

public export
Reflexive (Term syn ctx) (Equiv thy) where
    reflexive = IsEquiv (\env => Refl)

public export
Symmetric (Term syn ctx) (Equiv thy) where
    symmetric (IsEquiv xy) = IsEquiv (\env => sym $ xy env)

public export
Transitive (Term syn ctx) (Equiv thy) where
    transitive (IsEquiv xy) (IsEquiv yz) = IsEquiv (\env => trans (xy env) (yz env))

public export
Euclidean (Term syn ctx) (Equiv thy) where
    euclidean = euclidean @{TSE}

public export
Tolerance (Term syn ctx) (Equiv thy) where

public export
PartialEquivalence (Term syn ctx) (Equiv thy) where

public export
Equivalence (Term syn ctx) (Equiv thy) where
