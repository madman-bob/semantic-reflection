module Syntax.SingleSorted.Model.Property

import public Control.Relation

import public Syntax.SingleSorted.Model.Equiv
import public Syntax.SingleSorted.Term
import public Syntax.SingleSorted.Theory

%default total

||| Semantic property
|||
||| A semantic property for a term in a theory is a regular property for that
||| term, that can be transferred between equivalent terms.
public export
interface Property (0 thy : Theory syn) (0 p : Term syn ctx -> Type) where
    constructor MkProperty
    replace : {t : Term syn ctx} ->
              {s : Term syn ctx} ->
              Equiv thy t s ->
              p t ->
              p s

public export
{t : Term syn ctx} -> Property thy (Equiv thy t) where
    replace su ts = transitive ts su
