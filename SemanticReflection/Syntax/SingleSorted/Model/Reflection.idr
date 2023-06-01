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
openAx : (thyNm : Name) -> Axiom syn -> Elab ()
openAx thyNm ax = do
    name <- map (UN . Basic) $ unerase ax.name
    declare [
        IClaim fc MW Export [Totality Total] (MkTy fc fc name !prfTy),
        IDef fc name [PatClause fc !(prfLhs name) !prfRhs]
    ]
  where
    fc : FC
    fc = EmptyFC

    unerase : (0 x : a) -> Elab a
    unerase x = check !(quote x)

    ||| Requoting a previously checked %search might result in a partially computed value
    |||
    ||| Remaining holes in the value all get called ?sa, leading to name collisions.
    ||| So we change them to _, to restart evaluation.
    |||
    ||| Hopefully the user doesn't have any holes called ?sa.
    searchHack : TTImp -> TTImp
    searchHack = mapTTImp $ \case
        IHole fc "sa" => `(_)
        s => s

    prfTy : Elab TTImp
    prfTy = do
        vars <- unerase ax.vars

        let env = foldl
              (\rest, nm => `(~(rest) :< ~(IVar fc $ UN $ Basic nm)))
              `([<])
              vars

        lhs <- map searchHack $ quote ax.lhs
        rhs <- map searchHack $ quote ax.rhs

        let a = IVar fc $ UN $ Basic "a"
        let t = foldr
              (\nm, rest => IPi fc M0 ExplicitArg (Just nm) a rest)
              `(evalEnv ~(env) ~(lhs) === evalEnv ~(env) ~(rhs))
              (map (UN . Basic) vars)

        pure `({0 a : Type} -> Model ~(IVar fc thyNm) a => ~(t))

    prfLhs : Name -> Elab TTImp
    prfLhs name = do
        vars <- unerase ax.vars

        pure $ foldl
            (\rest, nm => IApp fc rest $ IBindVar fc nm)
            (IVar fc name)
            vars

    prfRhs : Elab TTImp
    prfRhs = do
        vars <- unerase ax.vars

        thy <- check $ IVar fc thyNm
        Just hasAx <- search $ HasAxiom thy ax
            | Nothing => fail "Axiom not part of theory"

        let prf = foldl
              (\rest, nm => IApp fc rest $ IVar fc $ UN $ Basic nm)
              `(getPrf {a} ~(!(quote hasAx)))
              vars

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
