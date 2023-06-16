module Language.Monoid.UnusedVar

import Data.Bool
import Data.Bool.Monoid

import Syntax.PreorderReasoning

import public Syntax.SingleSorted.Property.UnusedVar

import public Language.Monoid

%default total

%hide Prelude.(*)

||| We locally override `||`, as Prelude.(||) is lazy in its second argument
|||
||| This makes `cong2 (||) ...` more convenient.
(||) : Bool -> Bool -> Bool
x || y = Prelude.(||) x y

%hide Prelude.(||)

||| We make heavy use of the `Or` model in this file, so we define this shorthand
evalOr : Env ctx Bool -> Term MonoidSyn ctx -> Bool
evalOr env t = evalEnv @{Or} env t

||| We test whether a variable is used in a term, by evaluating it in the `Or`
||| model, in the indicator environment
|||
||| The rest of this file is proving that this is the correct thing to do.
evalInd : {ctx : Context} ->
          Elem nm ctx ->
          Term MonoidSyn ctx ->
          Bool
evalInd idx t = evalOr (indEnv False True idx) t

||| If a term evaluates to False, for a variable, then the variable is unused in
||| the term
evalIndFalseUnused : (t : Term MonoidSyn ctx) ->
                     (0 prf : evalInd i t = False) ->
                     UnusedVar MonoidThy i t
evalIndFalseUnused (Var j) prf = IsUnused $ \env, x => sym $ replaceDiff $ indEnvMiss absurd prf
evalIndFalseUnused (Operation (MkOp Here) [<l, r]) prf = IsUnused $ \env, x => do
    let 0 (lPrf, rPrf) = orBothFalse prf
    cong2 (*)
        ((evalIndFalseUnused l lPrf).canReplace _ _)
        ((evalIndFalseUnused r rPrf).canReplace _ _)
evalIndFalseUnused (Operation (MkOp (There Here)) [<]) prf = IsUnused $ \env, x => Refl

||| All terms evaluated in the constant False environment are False
evalFalse : {t : Term MonoidSyn ctx} -> evalOr (constEnv False) t = False
evalFalse {t = Var i} = constEnvConst
evalFalse {t = Operation (MkOp Here) [<l, r]} = cong2 (||) (evalFalse {t = l}) (evalFalse {t = r})
evalFalse {t = Operation (MkOp (There Here)) [<]} = Refl

||| We can decompose unuse in monoids
|||
||| This is not true in eg. groups, as `x` is used in `x`, and in `inv x`, but not
||| in `x * inv x`.
unusedMatch : UnusedVar MonoidThy {ctx} i (l * r) ->
              (UnusedVar MonoidThy i l, UnusedVar MonoidThy i r)
unusedMatch lrUnused = do
    let 0 lrFalse = Calc $
          |~ evalInd i l || evalInd i r
          ~~ evalOr (replace (constEnv False) i True) (l * r)
              ..<(cong (`evalOr` (l * r)) replaceConstInd)
          ~~ evalOr (constEnv False) (l * r)
              ..<(lrUnused.canReplace @{Or} (constEnv False) True)
          ~~ False
              ...(evalFalse {t = l * r})

    let 0 (lFalse, rFalse) = orBothFalse lrFalse

    (irrelevantUnusedVar $ evalIndFalseUnused l lFalse, irrelevantUnusedVar $ evalIndFalseUnused r rFalse)

||| If a variable is unused in a term, then the term evaluates to False, for that
||| variable
evalIndUnusedFalse : (t : Term MonoidSyn ctx) ->
                     UnusedVar MonoidThy i t ->
                     evalInd i t = False
evalIndUnusedFalse (Var j) iUnused = irrelevantEq $ Calc $
    |~ get (indEnv False True i) j
    ~~ get (replace (constEnv False) i True) j ..<(cong (`get` j) replaceConstInd)
    ~~ get (constEnv False) j                  ..<(iUnused.canReplace @{Or} (constEnv False) True)
    ~~ False                                   ...(constEnvConst)
evalIndUnusedFalse (Operation (MkOp Here) [<l, r]) iUnused = do
    let (lUnused, rUnused) = unusedMatch iUnused
    cong2 (||) (evalIndUnusedFalse l lUnused) (evalIndUnusedFalse r rUnused)
evalIndUnusedFalse (Operation (MkOp (There Here)) [<]) iUnused = Refl

export
isUnusedVar : {ctx : Context} ->
              (idx : Elem v ctx) ->
              (t : Term MonoidSyn ctx) ->
              Dec (UnusedVar MonoidThy idx t)
isUnusedVar idx t with (evalInd idx t) proof prf
  _ | False = Yes $ evalIndFalseUnused t prf
  _ | True = No $ \idxUnused => absurd $ Calc $
        |~ False
        ~~ evalInd idx t ..<(evalIndUnusedFalse t idxUnused)
        ~~ True          ...(prf)
