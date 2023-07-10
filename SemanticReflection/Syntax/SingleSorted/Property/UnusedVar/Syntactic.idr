module Syntax.SingleSorted.Property.UnusedVar.Syntactic

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Property.UnusedVar
import public Syntax.SingleSorted.Term

%default total

||| Syntactic notion of variable use in a term
|||
||| Points to where in the term a variable is used.
|||
||| This is not, in general, a semantic property.
|||
||| For example, in the theory of groups, `x` is used syntactically in `x * inv x`,
||| but not in `e`.
public export
data SynUsedVar : Elem nm ctx -> Term syn ctx -> Type where
    Here : {0 idx : Elem nm ctx} ->
           SynUsedVar idx (Var idx)
    There : {0 idx : Elem varNm ctx} ->
            {0 args : Env (anonCtx op.arity) (Term syn ctx)} ->
            (pos : Elem argNm (anonCtx op.arity)) ->
            SynUsedVar idx (get args pos) ->
            SynUsedVar idx (Operation op args)

||| If a variable is syntactically unused in an operation, then it is syntactically
||| unused in each of its arguments
export
synUnusedMatch : {syn : Syntax} ->
                 {op : Op syn} ->
                 {args : Env (anonCtx op.arity) (Term syn ctx)} ->
                 {0 i : Elem v ctx} ->
                 Not (SynUsedVar i (Operation op args)) ->
                 All args (Not . SynUsedVar i)
synUnusedMatch synUnused = allVars $ \idx, idxSynUsed => synUnused $ There idx idxSynUsed

||| Syntactic unuse implies semantic unuse
export
synUnusedUnused : (0 synUnused : Not (SynUsedVar {syn} {ctx} i t)) ->
                  UnusedVar thy i t
synUnusedUnused synUnused = irrelevantUnusedVar $ synUnusedUnused' synUnused
  where
    here : {0 i : Elem u ctx} ->
           {0 j : Elem v ctx} ->
           i = j ->
           SynUsedVar i (Var j)
    here Refl = Here

    synUnusedUnused' : {t : Term syn ctx} ->
                       Not (SynUsedVar i t) ->
                       UnusedVar thy i t
    synUnusedUnused' {t = Var j} synUnused = IsUnused $ \env, x => sym $ replaceDiff $ \ij => synUnused $ here ij
    synUnusedUnused' {t = Operation op args} synUnused = unusedCong $ assert_total $ mapAllVars synUnusedUnused' (synUnusedMatch synUnused)
