module Syntax.SingleSorted.Term.Base

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax

%default total

||| A term in a syntax and context
|||
||| For example, x * y is a term in the syntax of monoids, in the context
||| [<"x", "y"].
public export
data Term : (syn : Syntax) -> (ctx : Context) -> Type where
    Var : (idx : Elem v ctx) -> Term syn ctx
    Operation : (op : Op syn) -> (args : Env (anonCtx op.arity) (Term syn ctx)) -> Term syn ctx

%name Term t, s

||| Evaluate a term in an interpretation and environment
|||
||| This is unsafe as interpretations are not required to satisfy any laws.
public export
unsafeEvalEnv : Interp syn a =>
                Env ctx a ->
                Term syn ctx ->
                a
unsafeEvalEnv env (Var idx) = get env idx
unsafeEvalEnv env (Operation op args) = uncurry (impl op) $ assert_total $ map (unsafeEvalEnv env) args

||| Evaluate a term in an interpretation
|||
||| The term is interpreted as a function, taking its environment as arguments.
|||
||| This is unsafe as interpretations are not required to satisfy any laws.
public export
unsafeEval : Interp syn a =>
             {ctx : Context} ->
             Term syn ctx ->
             Fun ctx a
unsafeEval t = curry $ flip unsafeEvalEnv t

||| The substitution interpretation
|||
||| A substitution is a mapping from variables in one context to terms in another.
|||
||| A substitution is then applied to a term, in the first context, by replacing
||| each occurrence of each variable with the corresponding term.
|||
||| For example, substituting from context [<"x", "y"] to [<"a", "b", "c"] by
|||   x -> a
|||   y -> b * c
||| in
|||   x * y
||| gives
|||   a * (b * c)
public export
{syn : Syntax} -> Interp syn (Term syn ctx) where
    impl op = curry $ Operation op
