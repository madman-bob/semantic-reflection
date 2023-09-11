module Syntax.ManySorted.Term.Base

import public Syntax.ManySorted.Env
import public Syntax.ManySorted.Interpretation
import public Syntax.ManySorted.Syntax

%default total

||| A term in a syntax and context, of given sort
|||
||| For example, consider the syntax of sized monoids, and context `[x : 1; y : 2].
||| Then `x * y` is a term in this context, of sort 3.
public export
data Term : (syn : Syntax s) -> (ctx : Context s) -> (a : s) -> Type where
    Var : (var : Var ctx a) ->
          Term syn ctx a
    Operation : (op : Op syn) ->
                (i : Env op.index Prelude.id) ->
                (args : Env (anonCtx op.arity i) (Term syn ctx)) ->
                Term syn ctx (op.result i)

%name Term t, s

public export
varEnv : {ctx : Context s} ->
         Env ctx (Term syn ctx)
varEnv = map Var varEnv

||| Evaluate a term in an interpretation and environment
|||
||| This operation is sort-safe, but is unsafe as interpretations are not required
||| to satisfy any additional laws.
public export
unsafeEval : Interp syn u =>
             Env ctx u ->
             Term syn ctx a ->
             u a
unsafeEval env (Var idx) = get env idx
unsafeEval env (Operation op i args) = impl op i $ assert_total $ map (unsafeEval env) args

||| The substitution interpretation
|||
||| A substitution is a sort-preserving mapping from variables in one context to
||| terms in another.
|||
||| A substitution is then applied to a term, in the first context, by replacing
||| each occurrence of each variable with the corresponding term.
|||
||| For example, in the syntax of sized monoids, substituting from context
||| `[x : 4; y : 5] to `[a : 4; b : 3; c : 2] by
|||   x -> a
|||   y -> b * c
||| in
|||   x * y
||| gives
|||   a * (b * c)
public export
{syn : Syntax s} -> Interp syn (Term syn ctx) where
    impl = Operation
