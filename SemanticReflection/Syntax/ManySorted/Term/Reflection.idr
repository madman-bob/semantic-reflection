module Syntax.ManySorted.Term.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Interpretation
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term.Base

%default total

||| An implicit environment for a known context
|||
||| All values in the environment are implicit, and must be forced by use
impEnv : Context s -> TTImp
impEnv [<] = `([<])
impEnv (ctx :< _) = `(~(impEnv ctx) :< ~(Implicit EmptyFC False))

export
term : Syntax s ->
       TTImp ->
       Elab TTImp
term syn = term' []
  where
    term' : (args : List TTImp) ->
            TTImp ->
            Elab TTImp
    term' args (IVar fc (UN (Basic nm))) = do
        case !(catch $ findOp fc syn nm) of
            Nothing => case args of
                [] => pure asVar
                _ :: _ => failAt fc "Operation \{show nm} not in syntax"
            Just opT => asOp opT
      where
        asOp : (opT : TTImp) -> Elab TTImp
        asOp opT = do
            op <- check {expected = Op syn} opT

            if length op.arity == length args
               then pure ()
               else failAt fc "Operation \{show op.name} has arity \{show $ length op.arity}, given \{show $ length args} arg(s)"

            pure `(Operation ~(opT) ~(impEnv op.index) ~(snocListLit args))

        asVar : TTImp
        asVar = `(Var $ forgetName {nm = ~(IPrimVal EmptyFC $ Str nm)} %search)
    term' args (IApp fc f x) = do
        arg <- term' [] x
        term' (arg :: args) f
    term' args h@(IHole _ _) = pure h
    term' args t = failAt (getFC t) "Language does not support this construct"

%macro
export
fromTTImp : {syn : Syntax s} ->
            TTImp ->
            Elab (Term syn ctx a)
fromTTImp t = term syn t >>= check
