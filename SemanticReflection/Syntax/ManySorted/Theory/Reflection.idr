module Syntax.ManySorted.Theory.Reflection

import Control.Monad.State

import public Language.Reflection

import public Syntax.ManySorted.Theory.Base

%default total

record SchemaContext where
    constructor MkSchemaContext
    ops : SnocList String
    metas : SnocList String
    vars : Context TTImp

SchemaState : Type -> Type
SchemaState = State SchemaContext

addNm : (ignore : SnocList String) ->
        (nm : String) ->
        (nms : SnocList String) ->
        SnocList String
addNm ignore nm nms = if elem nm nms || elem nm ignore
    then nms
    else nms :< nm

bindVars : SnocList String -> TTImp -> (SnocList String, TTImp)
bindVars ignore t = runState [<] $ mapMTTImp (\case
    IBindVar fc nm => do
        modify $ addNm ignore nm
        pure $ IVar fc (UN (Basic nm))
    s => pure s) t

addMeta : String -> SchemaState ()
addMeta nm = modify {metas $= addNm [<] nm}

addVar : String ->
         TTImp ->
         SchemaState ()
addVar nm a = modify {vars $= (:< (nm :! a))}

addImpVar : String -> SchemaState ()
addImpVar nm = do
    let sortNm = nm ++ "Sort"
    addMeta sortNm
    addVar nm (IVar EmptyFC (UN (Basic sortNm)))

collectVars : TTImp -> SchemaState TTImp
collectVars (IPi fc MW ImplicitArg (Just (UN (Basic nm))) ty rhs) = do
    let (metas, ty) = bindVars !(gets ops) ty
    traverse_ addMeta metas
    addVar nm ty
    collectVars rhs
collectVars t = do
    let (impVars, t) = bindVars !(gets ops) t
    traverse_ addImpVar impVars
    pure t

axiom : Syntax s -> Decl -> Elab TTImp
axiom syn (IClaim _ MW Private [] (MkTy nmFc _ (UN (Basic nm)) t)) = do
    let fc = EmptyFC

    let ((MkSchemaContext _ metas vars), t) = runState (MkSchemaContext (map name syn.ops) [<] [<]) $ collectVars t

    let IAlternative _ FirstSuccess ((IApp _ (IApp _ (IVar _ `{Builtin.(===)}) lhs) rhs) :: _) = t
        | _ => fail "Expected axiom\neg. `[leftId : e * x = x]"

    let ctx = map fst vars

    metaVarsNm <- genSym "metaVars"

    lhsSortNm <- genSym "lhsSort"
    rhsSortNm <- genSym "rhsSort"

    lhs <- term syn ctx lhs
    rhs <- term syn ctx rhs

    pure $ ILocal fc [
            IClaim fc MW Private [] (MkTy fc fc metaVarsNm `(Context Type)),
            IDef fc metaVarsNm [PatClause fc (IVar fc metaVarsNm) (metaVarCtx metas)],

            IClaim fc MW Private [] (MkTy fc fc lhsSortNm `(ISort ~(IVar fc metaVarsNm) ?)),
            IDef fc lhsSortNm [PatClause fc (IVar fc lhsSortNm) !(introMetas metas `(?))],

            IClaim fc MW Private [] (MkTy fc fc rhsSortNm `(ISort ~(IVar fc metaVarsNm) ?)),
            IDef fc rhsSortNm [PatClause fc (IVar fc rhsSortNm) !(introMetas metas `(?))]
        ] `(MkAxiom
            ~(IPrimVal nmFc (Str nm))
            ~(IVar fc metaVarsNm)
            ~(!(varCtx metas vars))
            {lhsSort = ~(IVar fc lhsSortNm)}
            ~(!(introMetas metas lhs))
            {rhsSort = ~(IVar fc rhsSortNm)}
            ~(!(introMetas metas rhs))
        )
  where
    metaVarCtx : SnocList String -> TTImp
    metaVarCtx metas = snocListLit $ map (\nm => `(~(IPrimVal EmptyFC (Str nm)) :! _)) metas

    introMetas : SnocList String -> TTImp -> Elab TTImp
    introMetas metas body = do
        let fc = EmptyFC
        envNm <- genSym "env"
        pure $ ILam fc MW ExplicitArg (Just envNm) (Implicit fc False)
            (ICase fc [] (IVar fc envNm) (Implicit fc False) [
                PatClause fc
                    (snocListLit $ map (IBindVar fc) metas)
                    body
            ])

    varCtx : SnocList String -> SnocList (String, TTImp) -> Elab TTImp
    varCtx metas vars = map snocListLit $ traverse (\(nm, a) => pure `(~(IPrimVal EmptyFC (Str nm)) :! ~(!(introMetas metas a)))) vars
axiom syn decl = fail "Language does not support this construct"

namespace Axiom
    %macro
    export
    fromDecls : {syn : Syntax s} -> List Decl -> Elab (Axiom syn)
    fromDecls [decl] = axiom syn decl >>= check
    fromDecls _ = fail "Expected single axiom\nUse `Theory` for collections of axioms"

export
theory : Syntax s -> List Decl -> Elab TTImp
theory syn decls = map snocListLit $ traverse (axiom syn) decls

namespace Theory
    %macro
    export
    fromDecls : {syn : Syntax s} -> List Decl -> Elab (Theory syn)
    fromDecls decls = theory syn decls >>= check
