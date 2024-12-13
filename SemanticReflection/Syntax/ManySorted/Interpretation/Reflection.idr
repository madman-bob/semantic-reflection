module Syntax.ManySorted.Interpretation.Reflection

import public Control.Monad.State
import public Language.Reflection

import public Syntax.ManySorted.Interpretation.Base
import public Syntax.ManySorted.Syntax

%default total

export
snocListLit : Foldable f =>
              f TTImp ->
              TTImp
snocListLit xs = foldl
    (\xs, x => IApp EmptyFC (IApp EmptyFC (IVar EmptyFC `{(:<)}) xs) x)
    (IVar EmptyFC `{Lin})
    xs

export
findOp : FC ->
         Syntax s ->
         String ->
         Elab TTImp
findOp fc syn nm = do
    idx <- findOp' syn.rawOps
    pure `(MkOp ~(idx))
  where
    findOp' : (rawOps : SnocList (RawOp s)) -> Elab TTImp
    findOp' [<] = failAt fc "Operation \{show nm} not in syntax"
    findOp' (rawOps :< rawOp) = if rawOp.name == nm
        then pure `(Here)
        else do
            idx <- findOp' rawOps
            pure `(There ~(idx))

||| Define an interpretation of a syntax
|||
||| For example, in the syntax of sized monoids, we can define an interpretation on
||| Vect by:
|||
||| Interp SizedMonoidSyn (\n => Vect n a) where
|||     impl = `[
|||         e = []
|||         xs * ys = xs ++ ys
|||       ]
export
interpImpl : Syntax s ->
             List Decl ->
             Elab TTImp
interpImpl syn decls = do
    clauses <- for decls $ \case
        (IDef fc (UN $ Basic nm) [PatClause _ lhs rhs]) => do
            opT <- findOp fc syn nm
            op <- check {expected = Op syn} opT

            let args = execState [] $ collectVars lhs

            rhs <- openEnv (cast args) rhs
            rhs <- openEnv (map fst op.index) rhs

            pure $ PatClause EmptyFC opT rhs
        def => fail "Expected operation definition"

    mn <- genSym "lcase"
    pure $ ILam EmptyFC MW ExplicitArg (Just mn) (Implicit EmptyFC False) $
        ICase EmptyFC [] (IVar EmptyFC mn) (Implicit EmptyFC False) clauses
  where
    collectVars : TTImp -> State (List String) TTImp
    collectVars (IApp _ f (IBindVar _ nm)) = do
        modify (nm ::)
        collectVars f
    collectVars t = pure t

    openEnv : SnocList String -> TTImp -> Elab TTImp
    openEnv ctx rhs = do
        let vars = snocListLit $ map (IBindVar EmptyFC) ctx

        idxNm <- genSym "idx"
        pure $ ILam EmptyFC MW ExplicitArg (Just idxNm) (Implicit EmptyFC False)
            (ICase EmptyFC [] (IVar EmptyFC idxNm) (Implicit EmptyFC False)
                [PatClause EmptyFC vars rhs])

%macro
export
fromDecls : {syn : Syntax s} ->
            List Decl ->
            Elab (
                (op : Op syn) ->
                (i : Env op.index Prelude.id) ->
                Env (anonCtx op.arity i) u ->
                u (op.result i)
            )
fromDecls decls = check !(interpImpl syn decls)

namespace Interpretation
    %macro
    export
    fromDecls : {syn : Syntax s} ->
                List Decl ->
                Elab (Interp syn u)
    fromDecls decls = check `(MkInterp ~(!(interpImpl syn decls)))

||| Open a syntax in the current namespace
|||
||| This creates Idris-level equivalents of the operators in the syntax.
|||
||| For example, in the syntax of sized monoids, we already have the operators
||| - `(e) : Op SizedMonoidSyn
||| - `((*)) : Op SizedMonoidSyn
|||
||| This script creates Idris-level names for interpretations of these operators.
||| - e : Interp SizedMonoidSyn u => u 0
||| - (*) : Interp SizedMonoidSyn u => u n -> u m -> u (n + m)
export
openSyn : (synNm : Name) -> Elab ()
openSyn synNm = do
    s <- check $ Implicit fc False

    -- Cursed `map id` is non-trivial
    -- It seems to force evaluation of things that would otherwise end up as holes
    -- Maybe related to Idris issue #2993
    syn <- map id $ check {expected = Syntax s} $ IVar fc synNm

    for_ syn.ops $ \op => do
        let opNm = UN $ Basic op.name
        declare [
            IClaim $ MkFCVal fc $ MkIClaimData MW Public [Totality Total] (MkTy fc (MkFCVal fc opNm) !(opType op)),
            IDef fc opNm [PatClause fc (IVar fc opNm) !(opImpl op)]
        ]
  where
    fc : FC
    fc = EmptyFC

    ||| The type of a curried environment of types
    |||
    ||| For example, instead of the type
    |||   (env : Env `[x : Nat; y : String] id) -> p env
    ||| We use
    |||   (x : Nat) -> (y : String) -> p [<x, y]
    curryType : Context TTImp ->
                {default ExplicitArg argType : PiInfo TTImp} ->
                (ret : TTImp) ->
                TTImp
    curryType ctx ret =
        foldr (\(nm, a), t => IPi fc MW argType (maybeNm nm) a t) ret ctx
      where
        maybeNm : String -> Maybe Name
        maybeNm "" = Nothing
        maybeNm nm = Just (UN (Basic nm))

    opType : {syn : Syntax s} -> Op syn -> Elab TTImp
    opType op = do
        s <- quote s

        indexTypes <- for op.index $ \(nm, a) => [| (pure nm, quote a) |]

        let indexEnv = snocListLit $ map (IVar fc . UN . Basic . fst) indexTypes
        let sortInterp = \a => `(u (~(a) ~(indexEnv)))

        argSorts <- map cast $ for op.arity $ \a => quote a
        let argTypes = map (\argSort => ("", sortInterp argSort)) argSorts

        resultSort <- quote $ op.result

        pure `(
            {0 u : ~(s) -> Type} ->
            Interp ~(IVar fc synNm) u =>
            ~(curryType indexTypes {argType = ImplicitArg} $
                curryType argTypes $
                    sortInterp resultSort
            )
        )

    ||| For some reason, quoting an op results in ?syn holes where the syntax should be.
    ||| If we have multiple operations, this results in a "syn is already defined" error.
    ||| The `id` trick doesn't seem to work here.
    ||| This hack works around this issue.
    ||| Maybe related to Idris issue #2993
    synHoleHack : TTImp -> TTImp
    synHoleHack t = flip mapTTImp t $ \case
        IHole fc "syn" => IVar fc synNm
        t => t

    opImpl : {syn : Syntax s} ->
             Op syn ->
             Elab TTImp
    opImpl op = do
        let imp = Implicit fc False

        let indices = map (UN . Basic . fst) op.index
        args <- for op.arity $ \_ => genSym "x"

        pure $ foldr (\nm, t => ILam fc MW ExplicitArg (Just nm) imp t) `(
            impl
                {syn = ~(IVar fc synNm)}
                ~(synHoleHack !(quote op))
                ~(snocListLit $ map (IVar fc) indices)
                ~(snocListLit $ map (IVar fc) args)
            ) args
