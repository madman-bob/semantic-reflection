module Syntax.SingleSorted.Property.UnusedVar

import Syntax.PreorderReasoning

import public Syntax.SingleSorted

%default total

||| Proof that a variable is unused in a term, in a theory
|||
||| We say that a variable is unused in a term if, when evaluating that term, in any
||| model and environment, we can freely change the assignment of that variable,
||| without changing the result.
|||
||| Note that this is not the same as inspecting the term syntactically.
|||
||| For example, in the theory of groups, `x` is unused in `x * inv x`.
public export
record UnusedVar (thy : Theory syn) (i : Elem v ctx) (t : Term syn ctx) where
    constructor IsUnused
    canReplace : {0 a : Type} ->
                 Model thy a =>
                 (env : Env ctx a) ->
                 (x : a) ->
                 evalEnv env t = evalEnv (replace env i x) t

export
Property thy (UnusedVar thy i) where
    replace {t} {s} ts idxUnused = IsUnused $ \env, x => Calc $
        |~ evalEnv env s
        ~~ evalEnv env t               ..<(isEquiv @{ts} _)
        ~~ evalEnv (replace env i x) t ...(idxUnused.canReplace env x)
        ~~ evalEnv (replace env i x) s ...(isEquiv @{ts} _)

||| If a variable is unused in itself, then all models of that theory are trivial
|||
||| For example, consider the "constant" theory, with:
||| - a constant `e`
||| - the axiom `forall x. x = e`
|||
||| The constant theory is modeled by (), and has `x` unused in `x`.
export
unusedInSelf : (0 i : Elem nm ctx) ->
               UnusedVar thy i (Var i) ->
               Model thy a =>
               {0 x : a} ->
               {0 y : a} ->
               x = y
unusedInSelf i iUnused = irrelevantEq $ Calc $
    |~ x
    ~~ get (constEnv x) i               ..<(constEnvConst)
    ~~ get (replace (constEnv x) i y) i ...(iUnused.canReplace (constEnv x) y)
    ~~ y                                ...(replaceSame)

||| All variables are unused in other variables
export
unusedInOther : {0 i : Elem v ctx} ->
                {0 j : Elem u ctx} ->
                Not (i = j) ->
                UnusedVar thy i (Var j)
unusedInOther nij = IsUnused $ \env, x => sym $ replaceDiff nij
