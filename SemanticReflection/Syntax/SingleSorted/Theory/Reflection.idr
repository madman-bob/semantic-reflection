module Syntax.SingleSorted.Theory.Reflection

import public Control.Monad.State
import public Decidable.Equality

import public Language.Reflection

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term
import public Syntax.SingleSorted.Theory.Base
import public Syntax.SingleSorted.Theory.Proof

%default total

namespace Axiom
    public export
    axiom : {syn : Syntax} ->
            TTImp ->
            Elab (Axiom syn)
    axiom s@(IApp fc1 (IApp fc2 (IVar fc3 `{Builtin.(===)}) lhs) rhs) = do
        let ctx = usedVars (map name syn.ops) s

        lhs <- term lhs
        rhs <- term rhs

        pure $ MkAxiom ctx lhs rhs
      where
        addVarName : (ignore : Context) ->
                     TTImp ->
                     State Context TTImp
        addVarName ignore s@(IVar _ (UN $ Basic nm)) = do
            case isElem nm ignore of
                 Yes _ => pure ()
                 No _ => case isElem nm !get of
                     Yes _ => pure ()
                     No _ => modify (:< nm)
            pure s
        addVarName ignore s = pure s

        usedVars : (ignore : Context) ->
                   TTImp ->
                   Context
        usedVars ignore s = execState [<] $ mapMTTImp (addVarName ignore) s
    axiom (IAlternative _ FirstSuccess ss) = choice $ assert_total $ map (delay . axiom) ss
    axiom s = failAt (getFC s) "Expected axiom\neg. `(e * x = x)"

    %macro
    public export
    fromTTImp : {syn : Syntax} ->
                TTImp ->
                Elab (Axiom syn)
    fromTTImp s = axiom s

namespace Theory
    export
    theory : {syn : Syntax} -> TTImp -> Elab (Theory syn)
    theory (IApp _ (IApp _ (IVar _ `{(:<)}) xs) x) = [| theory xs :< axiom x |]
    theory (IVar _ `{Lin}) = [| [<] |]
    theory s = failAt (getFC s) "Expected theory\neg. `([<e * x = x, x * e = x])"

    %macro
    export
    fromTTImp : {syn : Syntax} -> TTImp -> Elab (Theory syn)
    fromTTImp s = theory s
