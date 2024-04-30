module Syntax.ManySorted.Theory.Proof

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Interpretation
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term
import public Syntax.ManySorted.Theory.Base

%default total

||| A proof that an interpretation satisfies an axiom schema
public export
interface SatAxiom (0 int : Interp {s} syn u) (0 ax : Axiom syn) where
    constructor MkSatAxiom
    prf : (metaEnv : Env ax.metaVars Prelude.id) ->
          (env : IEnv metaEnv ax.vars u) ->
          unsafeEval @{int} env (ax.lhs metaEnv) ~=~ unsafeEval @{int} env (ax.rhs metaEnv)

%name SatAxiom satAx

||| A proof that an interpretation satisfies a theory
public export
data SatTheory : Interp {s} syn u -> Theory syn -> Type where
    Lin : SatTheory int [<]
    (:<) : SatTheory int thy -> SatAxiom int axs -> SatTheory int (thy :< axs)

%name SatTheory satThy

public export
data HasAxiom : Theory syn -> Axiom syn -> Type where
    Here : HasAxiom (thy :< ax) ax
    There : HasAxiom thy ax -> HasAxiom (thy :< f) ax

%name HasAxiom hasAx

public export
getSatAxiom : SatTheory int thy =>
              HasAxiom thy ax ->
              SatAxiom int ax
getSatAxiom @{satThy :< sat} Here = sat
getSatAxiom @{satThy :< _} (There hasAx) = getSatAxiom hasAx
