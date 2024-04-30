module Syntax.ManySorted.Model.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Model.Base
import public Syntax.ManySorted.Theory

%default total

||| Open an axiom in the current namespace
|||
||| This creates an Idris-level accessor for proofs of the axiom.
|||
||| For example, in the theory of sized monoids, we have the axiom
||| `[assoc : x * (y * z) = (x * y) * z] : Axiom SizedMonoidSyn
|||
||| This script creates an Idris-level name to access proofs of that axiom.
||| assoc : Model SizedMonoidThy u =>
|||         (0 x : u n) ->
|||         (0 y : u m) ->
|||         (0 z : u p) ->
|||         x * (y * z) ~=~ (x * y) * z
export
openAx : (thyNm : Name) -> Axiom syn -> Elab ()
openAx thyNm ax = do
    name <- map (UN . Basic) $ unerase ax.name
    declare [
        IClaim fc MW Export [Totality Total] (MkTy fc fc name !prfTy),
        IDef fc name [PatClause fc (prfLhs name) !prfRhs]
    ]
  where
    fc : FC
    fc = EmptyFC

    unerase : (0 x : a) -> Elab a
    unerase x = check !(quote x)

    bindPis : {default ExplicitArg piInfo : PiInfo TTImp} ->
              Context TTImp ->
              TTImp ->
              TTImp
    bindPis {piInfo} args body = foldr (\(nm, a), rest => IPi fc M0 piInfo (Just (UN (Basic nm))) a rest) body args

    metaEnv : TTImp
    metaEnv = snocListLit $ map (\(nm, _) => IVar fc $ UN $ Basic nm) ax.metaVars

    env : TTImp
    env = snocListLit $ map (\(nm, _) => IVar fc $ UN $ Basic nm) ax.vars

    prfTy : Elab TTImp
    prfTy = do
        metaVars <- traverse (\(nm, a) => pure (nm, !(quote a))) ax.metaVars
        vars <- traverse (\(nm, a) => pure (nm, `(u (~(!(quote a)) ~(metaEnv))))) ax.vars

        pure `(
            {0 u : _ -> Type} ->
            {auto 0 _ : Model ~(IVar fc thyNm) u} ->
            ~(
                bindPis {piInfo = ImplicitArg} metaVars $
                bindPis vars
                `(eval ~(env) (~(!(quote ax.lhs)) ~(metaEnv)) ~=~ eval ~(env) (~(!(quote ax.rhs)) ~(metaEnv)))
              )
        )

    prfLhs : Name -> TTImp
    prfLhs name = foldl
            (\rest, (nm, _) => IApp fc rest $ IBindVar fc nm)
            (IVar fc name)
            ax.vars

    prfRhs : Elab TTImp
    prfRhs = do
        thy <- check $ IVar fc thyNm

        Just hasAx <- search $ HasAxiom thy ax
            | Nothing => fail "Axiom not part of theory"

        pure `(irrelevantEq $ getPrf ~(!(quote hasAx)) ~(metaEnv) ~(env))

||| Open a theory in the current namespace
|||
||| This creates Idris-level accessors for proofs of the theory.
|||
||| For example, in the theory of sized monoids, we have the axioms
||| - `[leftId : {x : n} -> e * x = x] : Axiom SizedMonoidSyn
||| - `[rightId : {x : n} -> x * e = x] : Axiom SizedMonoidSyn
||| - `[assoc : {x : n} -> {y : m} -> {z : p} -> x * (y * z) = (x * y) * z] : Axiom SizedMonoidSyn
|||
||| This script creates Idris-level names to access proofs of that axiom.
||| - leftId : Model SizedMonoidThy u => (0 x : u n) -> SizedMonoid.e * x = x
||| - rightId : Model SizedMonoidThy u => (0 x : u n) -> x * SizedMonoid.e = x
||| - assoc : Model SizedMonoidThy u =>
|||           (0 x : u n) ->
|||           (0 y : u m) ->
|||           (0 z : u p) ->
|||           x * (y * z) ~=~ (x * y) * z
export
openThy : (thyNm : Name) -> Elab ()
openThy thyNm = do
    s <- check `(_)
    syn <- check `(_)
    thy <- check {expected = Theory {s} syn} $ IVar EmptyFC thyNm
    axFor thy (openAx thyNm)
  where
    axFor : Theory syn -> (Axiom syn -> Elab ()) -> Elab ()
    axFor [<] f = pure ()
    axFor (thy :< ax) f = do
        axFor thy f
        f ax
