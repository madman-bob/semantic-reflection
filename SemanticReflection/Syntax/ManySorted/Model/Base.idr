module Syntax.ManySorted.Model.Base

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Interpretation
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term
import public Syntax.ManySorted.Theory

%default total

||| A model of a theory is
||| - an interpretation of the underlying syntax
||| - proof that interpretation satisfies the laws of the theory
|||
||| For example, in the syntax of sized monoids, we could take
||| - (\n => Vect n a) as our collection of values
||| - [] as our identity
||| - concatenation as our binary operation
||| - proofs that this satisfies sized monoid laws
public export
interface Model (0 thy : Theory {s} syn) (0 u : s -> Type) | u where
    constructor MkModel
    int : Interp syn u
    satThy : SatTheory int thy

%name Model mdl

%hint
public export
interp : Model {syn} thy u -> Interp syn u
interp mdl = int

||| Evaluate a term in a model and environment
public export
eval : Model {syn} thy u =>
       Env ctx u ->
       Term syn ctx a ->
       u a
eval =
    -- safety enforced by existence of satThy
    unsafeEval @{int}

public export
getPrf : Model thy u =>
         HasAxiom thy ax ->
         (metaEnv : Env ax.metaVars Prelude.id) ->
         (env : IEnv metaEnv ax.vars u) ->
         unsafeEval @{Base.int} env (ax.lhs metaEnv) ~=~ unsafeEval @{Base.int} env (ax.rhs metaEnv)
getPrf hasAx = prf @{getSatAxiom @{satThy} hasAx}
