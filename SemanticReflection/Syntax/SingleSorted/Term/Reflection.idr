module Syntax.SingleSorted.Term.Reflection

import public Decidable.Equality

import public Syntax.SingleSorted.Interpretation
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term.Base

%default total

export
term : {syn : Syntax} ->
       {ctx : Context} ->
       TTImp ->
       Elab (Term syn ctx)
term = term' []
  where
    term' : (args : ConsEnv nms (Term syn ctx)) ->
            TTImp ->
            Elab (Term syn ctx)
    term' args (IVar fc (UN (Basic nm))) = lookupOperation nm <|> lookupVar nm
      where
        lookupOperation : String -> Elab (Term syn ctx)
        lookupOperation nm = case findOp {syn} nm of
            Just op => case collect args of
                Just args => pure $ Operation op args
                Nothing => failAt fc "Operation has arity \{show op.arity}, given \{show $ length args} args"
            Nothing => failAt fc "Operation \{show nm} not in signature"

        lookupVar : String -> Elab (Term syn ctx)
        lookupVar nm = case !(search $ Elem nm ctx) of
            Just idx => case args of
                [] => pure $ Var idx
                _ :: _ => failAt fc "Variable \{show nm} is not a function"
            Nothing => failAt fc "Variable \{show nm} not in context \{show ctx}"
    term' args (IApp fc f x) = do
        x <- term' [] x
        term' ((::) x args {nm = ""}) f
    term' args h@(IHole _ _) = check h
    term' args s = failAt (getFC s) "Language does not support this construct"

%macro
export
fromTTImp : {syn : Syntax} ->
            {ctx : Context} ->
            TTImp ->
            Elab (Term syn ctx)
fromTTImp s = term s
