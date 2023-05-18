module Syntax.SingleSorted.Theory.Proof

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term
import public Syntax.SingleSorted.Theory.Base

%default total

||| A proof that an interpretation satisfies an axiom
public export
interface SatAxiom (0 int : Interp syn a) (0 ax : Axiom syn) where
    constructor Prf
    prf : Fun' ax.vars a $ \env => unsafeEvalEnv @{int} env ax.lhs = unsafeEvalEnv @{int} env ax.rhs

%name SatAxiom sat

||| A proof that an interpretation satisfies a theory
public export
data SatTheory : Interp syn a -> Theory syn -> Type where
    Lin : SatTheory int [<]
    (:<) : SatTheory int thy -> SatAxiom int ax -> SatTheory int (thy :< ax)

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
