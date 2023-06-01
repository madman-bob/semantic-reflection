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
    getFC : Decl -> FC
    getFC (IClaim fc _ _ _ _) = fc
    getFC (IData fc _ _ _) = fc
    getFC (IDef fc _ _) = fc
    getFC (IParameters fc _ _) = fc
    getFC (IRecord fc _ _ _ _) = fc
    getFC (INamespace fc _ _) = fc
    getFC (ITransform fc _ _ _) = fc
    getFC (IRunElabDecl fc _) = fc
    getFC (ILog _) = EmptyFC
    getFC (IBuiltin fc _ _) = fc

    export
    axiom : {syn : Syntax} ->
            List Decl ->
            Elab (Axiom syn)
    axiom [IClaim fc MW Private [] (MkTy _ _ (UN (Basic nm)) $ IAlternative _ FirstSuccess [s@(IApp _ (IApp _ (IVar _ `{Builtin.(===)}) lhs) rhs), _])] = do
        let ctx = usedVars (map name syn.ops) s

        lhs <- term lhs
        rhs <- term rhs

        pure $ MkAxiom nm ctx lhs rhs
      where
        addVarName : (ignore : Context) ->
                     TTImp ->
                     State Context TTImp
        addVarName ignore s@(IBindVar _ nm) = do
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
    axiom (decl :: _ :: _) = failAt (getFC decl) "Expected single axiom\nUse `Theory` for collections of axioms"
    axiom decls = failAt (maybe EmptyFC getFC $ head' decls) "Expected axiom\neg. `[leftId : e * x = x]"

    %macro
    export
    fromDecls : {syn : Syntax} ->
                List Decl ->
                Elab (Axiom syn)
    fromDecls s = axiom s

namespace Theory
    export
    theory : {syn : Syntax} -> List Decl -> Elab (Theory syn)
    theory decls = theory' (cast decls)
      where
        theory' : SnocList Decl -> Elab (Theory syn)
        theory' (decls :< decl) = [| theory' decls :< axiom [decl] |]
        theory' [<] = [| [<] |]

    %macro
    export
    fromDecls : {syn : Syntax} -> List Decl -> Elab (Theory syn)
    fromDecls s = theory s
