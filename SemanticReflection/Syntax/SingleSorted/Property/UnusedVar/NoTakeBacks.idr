module Syntax.SingleSorted.Property.UnusedVar.NoTakeBacks

import Data.Bool
import Syntax.PreorderReasoning

import public Syntax.SingleSorted.Interpretation.Env.All
import Syntax.SingleSorted.Interpretation.Env.Any
import public Syntax.SingleSorted.Property.UnusedVar
import public Syntax.SingleSorted.Property.UnusedVar.Syntactic

%default total

||| We locally override `||`, as Prelude.(||) is lazy in its second argument
|||
||| This makes `cong2 (||) ...` more convenient.
(||) : Bool -> Bool -> Bool
x || y = Prelude.(||) x y

%hide Prelude.(||)

namespace Axiom
    ||| An equational axiom has no take backs when all variables are used on both sides
    ||| of the equation
    |||
    ||| Examples of axioms with no take backs:
    ||| - Associativity: x * (y * z) = (x * y) * z
    ||| - Distributivity: x * (y + z) = x * y + x * z
    ||| - Rotation of a ternary operator: <x, y, z> = <z, x, y>
    |||
    ||| Examples of axioms *with* take backs:
    ||| - Inverses: x * inv x = e
    ||| - Absorption: 0 * x = 0
    ||| - Ternary majority axioms: eg. <x, y, y> = y
    public export
    record NoTakeBacks (ax : Axiom syn) where
        constructor MkNoTakeBacks
        lAllUsed : AllVars ax.vars (\idx => SynUsedVar idx ax.lhs)
        rAllUsed : AllVars ax.vars (\idx => SynUsedVar idx ax.rhs)

||| A theory has no take backs when all its axioms have no take backs
public export
data NoTakeBacks : Theory syn -> Type where
    Lin : NoTakeBacks [<]
    (:<) : NoTakeBacks thy ->
           NoTakeBacks ax ->
           NoTakeBacks (thy :< ax)

||| Returns True if any value in the environment is True
any : Env ctx Bool -> Bool
any [<] = False
any (env :< x) = x || any env

||| We will consider the "Or" interpretation, where all operations take the Boolean
||| or of their arguments
|||
||| We will show that the Or interpretation is a model for theories with no take
||| backs, and that it can be used to detect variable use.
OrInterp : {syn : Syntax} -> Interp syn Bool
OrInterp = MkInterp $ \op => curry any

||| We define this shorthand for evaluation in the Or interpretation
|||
||| This is unsafe, as we have yet to prove that the Or interpretation is a model.
evalOr : {syn : Syntax} ->
         Env ctx Bool ->
         Term syn ctx ->
         Bool
evalOr = unsafeEvalEnv @{OrInterp}

||| In a Boolean environment, either all values are False, or there is a True
|||
||| There may be multiple Trues, but we only need one of them.
|||
||| If all values are False, then `env = constEnv False`, but we find it more
||| convenient to use `All env (=== False)`.
|||
||| We call environments with all False values False environments, and environments
||| with a True value True environments.
|||
||| All environments are either True environments, or False environments.
findTrue : (env : Env ctx Bool) ->
           Either
               (All env (=== False))
               (Any env (=== True))
findTrue [<] = Left [<]
findTrue (env :< False) = bimap
    (\allFalse => allFalse :< Refl)
    (\someTrue => There someTrue)
    (findTrue env)
findTrue (env :< True) = Right $ Here Refl

||| Taking `any` of a False environment results in False
anyFalse : {env : Env ctx Bool} ->
           All env (=== False) ->
           any env = False
anyFalse {env = [<]} [<] = Refl
anyFalse {env = env :< x} (restFalse :< xFalse) = cong2 (||) xFalse (anyFalse restFalse)

||| If the `any` of an environment is False, then all values of the environment are False
anyFalse' : {env : Env ctx Bool} ->
            {idx : Elem nm ctx} ->
            any env = False ->
            get env idx = False
anyFalse' {env = env :< x} {idx = Here} prf = fst $ orBothFalse prf
anyFalse' {env = env :< x} {idx = There idx} prf = anyFalse' {env} {idx} $ snd $ orBothFalse prf

||| Taking `any` of a True environment results in True
anyTrue : {idx : Elem nm ctx} ->
          {env : Env ctx Bool} ->
          get env idx = True ->
          any env = True
anyTrue {idx = Here} {env = env :< True} Refl = Refl
anyTrue {idx = There idx} {env = env :< x} idxTrue = Calc $
    |~ x || any env
    ~~ x || True    ...(cong (x ||) $ anyTrue {idx} {env} idxTrue)
    ~~ True         ...(orTrueTrue x)

||| If the `any` of an environment is True, then there is a True in the environment
anyTrue' : {env : Env ctx Bool} ->
           any env = True ->
           Exists $ \nm => (idx : Elem nm ctx ** get env idx = True)
anyTrue' {env = [<]} prf = absurd prf
anyTrue' {env = env :< False} prf = bimap id (\(idx ** idxTrue) => (There idx ** idxTrue)) $ anyTrue' {env} prf
anyTrue' {env = env :< True} prf = Evidence _ (Here ** Refl)

||| The `Or` interpretation of any term in a False environment is False
orFalse : {t : Term syn ctx} ->
          All env (=== False) ->
          evalOr env t = False
orFalse {t = Var idx} allFalse = getAll allFalse idx
orFalse {t = Operation op args} allFalse = do
    let 0 evalArgsFalse = allVars $ \idx => Calc $
          |~ get (map (evalOr env) args) idx
          ~~ evalOr env (get args idx)       ...(getMap)
          ~~ False                           ...(orFalse {t = assert_smaller args $ get args idx} allFalse)
    Calc $
        |~ evalOr env (Operation op args)
        ~~ any (map (evalOr env) args)    ...(uncurryCurry)
        ~~ False                          ...(anyFalse evalArgsFalse)

||| When a variable used syntactically in a term is assigned True, then the `Or`
||| interpretation of that term is True
orTrue : {t : Term syn ctx} ->
         {0 idx : Elem nm ctx} ->
         SynUsedVar idx t ->
         get env idx = True ->
         evalOr env t = True
orTrue {t = Var idx} Here idxTrue = idxTrue
orTrue {t = Operation op args} (There pos idxUsed) idxTrue = do
    let 0 posTrue = Calc $
          |~ get (map (evalOr env) args) pos
          ~~ evalOr env (get args pos)       ...(getMap)
          ~~ True                            ...(orTrue idxUsed idxTrue)
    Calc $
        |~ evalOr env (Operation op args)
        ~~ any (map (evalOr env) args)    ...(uncurryCurry)
        ~~ True                           ...(anyTrue posTrue)

||| If an axiom has no take backs, then it is satisfied by the Or interpretation
satAx : {ax : Axiom syn} ->
        NoTakeBacks ax =>
        SatAxiom OrInterp ax
satAx @{ntb} = Prf $ Fun.curry $ \env => case findTrue env of
    Left allFalse => Calc $
        |~ evalOr env ax.lhs
        ~~ False                          ...(orFalse allFalse)
        ~~ evalOr env ax.rhs              ..<(orFalse allFalse)
    Right someTrue => do
        let Evidence nm (idx ** idxTrue) = getAny someTrue
        let idxUsedL = getAll ntb.lAllUsed idx
        let idxUsedR = getAll ntb.rAllUsed idx
        Calc $
            |~ evalOr env ax.lhs
            ~~ True              ...(orTrue idxUsedL idxTrue)
            ~~ evalOr env ax.rhs ..<(orTrue idxUsedR idxTrue)

||| If a theory has no take backs, then it is satisfied by the Or interpretation
satThy : {thy : Theory syn} ->
         NoTakeBacks thy =>
         SatTheory OrInterp thy
satThy {thy = [<]} @{[<]} = [<]
satThy {thy = thy :< ax} @{_ :< _} = satThy {thy} :< satAx {ax}

||| The Or interpretation is a model for a theory with no take backs
Or : {syn : Syntax} ->
     {thy : Theory syn} ->
     NoTakeBacks thy =>
     Model thy Bool
Or = MkModel OrInterp satThy

||| We define this shorthand for evaluation in the Or interpretation, and indicator
||| environment
|||
||| It remains to be shown that this detects variable use.
evalInd : {syn : Syntax} ->
          {ctx : Context} ->
          Elem nm ctx ->
          Term syn ctx ->
          Bool
evalInd idx = evalOr (indEnv False True idx)

||| If a term evaluates to False in the indicator environment, then that variable is
||| not used syntactically in the term
evalIndFalseUnused : {t : Term syn ctx} ->
                     evalInd i t = False ->
                     Not (SynUsedVar i t)
evalIndFalseUnused {t = Var i} iFalse Here = absurd $ Calc $
    |~ False
    ~~ get (indEnv False True i) i ..<(iFalse)
    ~~ True                        ...(indEnvSame)
evalIndFalseUnused {t = Operation op env} iFalse (There pos posUsed) = do
    let posFalse = trans (sym getMap) $ anyFalse' $ trans (sym uncurryCurry) iFalse
    evalIndFalseUnused {t = assert_smaller env $ get env pos} posFalse posUsed

||| If an operation is semantically unused in a theory with no take backs, then each
||| argument is also unused
unusedMatch : {0 args : Env (anonCtx op.arity) (Term syn ctx)} ->
              {0 pos : Elem nm (anonCtx op.arity)} ->
              NoTakeBacks thy =>
              UnusedVar thy i (Operation op args) ->
              UnusedVar thy i (get args pos)
unusedMatch iUnused = do
    let 0 argsFalse = Calc $
          |~ any (map (evalInd i) args)
          ~~ evalInd i (Operation op args)
              ..<(uncurryCurry)
          ~~ evalOr (replace (constEnv False) i True) (Operation op args)
              ..<(cong (`evalOr` Operation op args) replaceConstInd)
          ~~ evalOr (constEnv False) (Operation op args)
              ..<(iUnused.canReplace @{Or} (constEnv False) True)
          ~~ False
              ...(orFalse {t = Operation op args} $ allVars $ \idx => constEnvConst)
    let 0 posFalse = Calc $
          |~ evalInd i (get args pos)
          ~~ get (map (evalInd i) args) pos ..<(getMap)
          ~~ False                          ...(anyFalse' argsFalse)
    synUnusedUnused $ evalIndFalseUnused posFalse

||| If a term evaluates to True in the indicator environment, then that variable is
||| used semantically in the term in a theory with no take backs
evalIndTrueUsed : {t : Term syn ctx} ->
                  evalInd i t = True ->
                  NoTakeBacks thy =>
                  Not (UnusedVar thy i t)
evalIndTrueUsed {t = Var idx} iTrue iUnused = absurd $ Calc $
    |~ True
    ~~ get (indEnv False True i) idx             ..<(iTrue)
    ~~ get (replace (constEnv False) i True) idx ..<(cong (`get` idx) replaceConstInd)
    ~~ get (constEnv False) idx                  ..<(iUnused.canReplace @{Or} (constEnv False) True)
    ~~ False                                     ...(constEnvConst)
evalIndTrueUsed {t = Operation op args} iTrue iUnused = void $ do
    let Evidence nm (pos ** posTrue) = anyTrue' $ trans (sym uncurryCurry) iTrue
    evalIndTrueUsed {t = assert_smaller args $ get args pos} (trans (sym getMap) posTrue) $ unusedMatch iUnused

export
isUnusedVar : {syn : Syntax} ->
              {0 thy : Theory syn} ->
              NoTakeBacks thy =>
              {ctx : Context} ->
              (idx : Elem v ctx) ->
              (t : Term syn ctx) ->
              Dec (UnusedVar thy idx t)
isUnusedVar idx t with (evalInd idx t) proof prf
  _ | False = Yes $ synUnusedUnused $ evalIndFalseUnused prf
  _ | True = No $ evalIndTrueUsed prf
