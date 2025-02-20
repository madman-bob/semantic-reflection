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
    getFC (IClaim (MkFCVal fc _)) = fc
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
    axiom : Syntax ->
            Decl ->
            Elab TTImp
    axiom syn (IClaim $ MkFCVal _ $ MkIClaimData MW Private [] (MkTy _ (MkFCVal fc $ UN (Basic nm)) $ IAlternative _ FirstSuccess [s@(IApp _ (IApp _ (IVar _ `{(===)}) lhs) rhs), _])) = do
        let nm = IPrimVal fc $ Str nm
        let ctx = snocListLit $ map (IPrimVal EmptyFC . Str) $ usedVars (map name syn.ops) s

        lhs <- term syn lhs
        rhs <- term syn rhs

        pure `(MkAxiom ~(nm) ~(ctx) ~(lhs) ~(rhs))
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
    axiom syn decl = failAt (getFC decl) "Expected axiom\neg. `[leftId : e * x = x]"

    %macro
    export
    fromDecls : {syn : Syntax} ->
                List Decl ->
                Elab (Axiom syn)
    fromDecls [decl] = check !(axiom syn decl)
    fromDecls decls = failAt (maybe EmptyFC getFC $ head' decls) "Expected single axiom\nUse `Theory` for collections of axioms"

namespace Theory
    export
    theory : Syntax -> List Decl -> Elab TTImp
    theory syn decls = map snocListLit $ traverse (axiom syn) decls

    %macro
    export
    fromDecls : {syn : Syntax} -> List Decl -> Elab (Theory syn)
    fromDecls decls = check !(theory syn decls)
