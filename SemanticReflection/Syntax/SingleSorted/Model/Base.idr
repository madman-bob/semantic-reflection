module Syntax.SingleSorted.Model.Base

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term
import public Syntax.SingleSorted.Theory

%default total

||| A model of a theory is
||| - an interpretation of the underlying syntax
||| - proof that interpretation satisfies the laws of the theory
|||
||| For example, in the syntax of monoids, we could take
||| - Integer as our collection of values
||| - 0 as our identity
||| - addition as our binary operation
||| - proofs that this satisfies monoid laws
public export
interface Model (0 thy : Theory syn) (0 a : Type) | a where
    constructor MkModel
    int : Interp syn a
    satThy : SatTheory int thy

%name Model mdl

%hint
public export
interp : Model {syn} thy a -> Interp syn a
interp mdl = int

||| Evaluate a term in a model and environment
public export
evalEnv : Model {syn} thy a =>
          Env ctx a ->
          Term syn ctx ->
          a
evalEnv =
    -- safety enforced by existence of satThy
    unsafeEvalEnv @{int}

||| Evaluate a term in a model
|||
||| The term is interpreted as a function, taking its environment as arguments.
public export
eval : Model {syn} thy a =>
       {ctx : Context} ->
       Term syn ctx ->
       Fun ctx a
eval =
    -- safety enforced by existence of satThy
    unsafeEval @{int}

public export
getPrf : Model thy a =>
         HasAxiom thy ax ->
         Fun' ax.vars a $ \env => evalEnv env ax.lhs = evalEnv env ax.rhs
getPrf hasAx = prf @{getSatAxiom @{satThy} hasAx}
