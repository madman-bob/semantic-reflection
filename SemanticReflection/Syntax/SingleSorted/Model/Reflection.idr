module Syntax.SingleSorted.Model.Reflection

import public Language.Reflection

import public Syntax.SingleSorted.Model.Base
import public Syntax.SingleSorted.Theory

%default total

||| Open an axiom in the current namespace
|||
||| This creates an Idris-level accessor for proofs of the axiom.
|||
||| For example, in the theory of monoids, we have the axiom
||| `[assoc : x * (y * z) = (x * y) * z] : Axiom MonoidSyn
|||
||| This script creates an Idris-level name to access proofs of that axiom.
||| assoc : Model MonoidThy a =>
|||         (0 x : a) ->
|||         (0 y : a) ->
|||         (0 z : a) ->
|||         x * (y * z) = (x * y) * z
export
openAx : {syn : Syntax} -> (thyNm : Name) -> Axiom syn -> Elab ()
openAx thyNm ax = do
    let name = UN $ Basic ax.name
    declare [
        IClaim $ MkFCVal fc $ MkIClaimData MW Export [Totality Total] (MkTy fc (MkFCVal fc name) !prfTy),
        IDef fc name [PatClause fc !(prfLhs name) !prfRhs]
    ]
  where
    fc : FC
    fc = EmptyFC

    ttImpEnv : {ctx : Context} -> Env ctx TTImp
    ttImpEnv {ctx = [<]} = [<]
    ttImpEnv {ctx = ctx :< nm} = ttImpEnv {ctx} :< IVar fc (UN $ Basic nm)

    Interp syn TTImp where
        impl op = Fun.curry $ foldl (IApp fc) (IVar fc $ UN $ Basic op.name)

    idrTerm : {ctx : Context} -> Term syn ctx -> TTImp
    idrTerm t = unsafeEvalEnv ttImpEnv t

    prfTy : Elab TTImp
    prfTy = do
        let env = snocListLit $ map (\nm => IVar fc $ UN $ Basic nm) ax.vars

        let lhs = idrTerm ax.lhs
        let rhs = idrTerm ax.rhs

        let a = IVar fc $ UN $ Basic "a"
        let t = foldr
              (\nm, rest => IPi fc M0 ExplicitArg (Just nm) a rest)
              `(~(lhs) === ~(rhs))
              (map (UN . Basic) ax.vars)

        pure `({0 a : Type} -> Model ~(IVar fc thyNm) a => ~(t))

    prfLhs : Name -> Elab TTImp
    prfLhs name = do
        pure $ foldl
            (\rest, nm => IApp fc rest $ IBindVar fc nm)
            (IVar fc name)
            ax.vars

    prfRhs : Elab TTImp
    prfRhs = do
        thy <- check $ IVar fc thyNm
        Just hasAx <- search $ HasAxiom thy ax
            | Nothing => fail "Axiom not part of theory"

        let prf = foldl
              (\rest, nm => IApp fc rest $ IVar fc $ UN $ Basic nm)
              `(getPrf {a} ~(!(quote hasAx)))
              ax.vars

        pure `(irrelevantEq ~(prf))

||| Open a theory in the current namespace
|||
||| This creates Idris-level accessors for proofs of the theory.
|||
||| For example, in the theory of monoids, we have the axioms
||| - `[assoc : x * (y * z) = (x * y) * z] : Axiom MonoidSyn
||| - `[leftId : e * x = x] : Axiom MonoidSyn
||| - `[rightId : x * e = x] : Axiom MonoidSyn
|||
||| This script creates Idris-level names to access proofs of that axiom.
||| - assoc : Model MonoidThy a =>
|||           (0 x : a) ->
|||           (0 y : a) ->
|||           (0 z : a) ->
|||           x * (y * z) = (x * y) * z
||| - leftId : Model MonoidThy a => (0 x : a) -> Monoid.e * x = x
||| - rightId : Model MonoidThy a => (0 x : a) -> x * Monoid.e = x
export
openThy : (thyNm : Name) -> Elab ()
openThy thyNm = do
    let fc = EmptyFC
    syn <- check `(_)
    thy <- check {expected = Theory syn} $ IVar fc thyNm
    axFor thy (openAx thyNm)
  where
    axFor : Theory syn -> (Axiom syn -> Elab ()) -> Elab ()
    axFor [<] f = pure ()
    axFor (thy :< ax) f = do
        axFor thy f
        f ax
