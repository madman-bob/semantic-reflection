module Syntax.ManySorted.Interpretation.Reflection

import public Control.Monad.State
import public Language.Reflection

import public Syntax.ManySorted.Interpretation.Base
import public Syntax.ManySorted.Syntax

%default total

snocListLit : Foldable f =>
              f TTImp ->
              TTImp
snocListLit xs = foldl
    (\xs, x => IApp EmptyFC (IApp EmptyFC (IVar EmptyFC `{(:<)}) xs) x)
    (IVar EmptyFC `{Lin})
    xs

||| Define an interpretation of a syntax, by pattern matching on the syntax
||| operations
|||
||| For example, in the syntax of sized monoids, we can define an interpretation on
||| Vect by:
|||
||| Interp SizedMonoidSyn (\n => Vect n a) where
|||     impl = `(\case
|||         e => []
|||         xs * ys => xs ++ ys
|||       )
export
interpImpl : {syn : Syntax s} ->
             TTImp ->
             Elab (
                 (op : Op syn) ->
                 (i : Env op.index Prelude.id) ->
                 Env (anonCtx op.arity i) u ->
                 u (op.result i)
             )
interpImpl (ILam fc MW ExplicitArg mn arg $ ICase fc' opts t ty clauses) = do
    clauses <- for clauses $ \case
        PatClause fc lhs rhs => do
            let (args, opCode) = runState [] $ collectVars lhs

            -- Cursed `map id` is non-trivial
            -- It seems to force evaluation of things that would otherwise end up as holes
            -- Maybe related to Idris issue #2993
            op <- map id $ operation {syn} opCode

            rhs <- openEnv (cast args) rhs
            rhs <- openEnv (map fst op.index) rhs

            pure $ PatClause fc !(quote op) rhs
        clause => failAt fc "Expected operator case block with pattern clauses"

    check $ ILam fc MW ExplicitArg mn arg $ ICase fc' opts t ty clauses
  where
    collectVars : TTImp -> State (List String) TTImp
    collectVars (IApp _ f (IBindVar _ nm)) = do
        modify (nm ::)
        collectVars f
    collectVars t = pure t

    openEnv : SnocList String -> TTImp -> Elab TTImp
    openEnv ctx rhs = do
        let vars = snocListLit $ map (IBindVar fc) ctx

        idxNm <- genSym "idx"
        pure $ ILam fc MW ExplicitArg (Just idxNm) (Implicit fc False)
            (ICase fc [] (IVar fc idxNm) (Implicit fc False)
                [PatClause fc vars rhs])
interpImpl t = failAt (getFC t) "Expected operator case block"

%macro
export
fromTTImp : {syn : Syntax s} ->
            TTImp ->
            Elab (
                (op : Op syn) ->
                (i : Env op.index Prelude.id) ->
                Env (anonCtx op.arity i) u ->
                u (op.result i)
            )
fromTTImp t = interpImpl t

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
            IClaim fc MW Public [Totality Total] (MkTy fc fc opNm !(opType op)),
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
