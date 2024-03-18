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

findOp : FC ->
         Syntax s ->
         String ->
         Elab TTImp
findOp fc syn nm = do
    idx <- findOp' syn.rawOps
    pure `(MkOp ~(idx))
  where
    findOp' : (rawOps : SnocList (RawOp s)) -> Elab TTImp
    findOp' [<] = failAt fc "Operation \{show nm} not in syntax"
    findOp' (rawOps :< rawOp) = if rawOp.name == nm
        then pure `(Here)
        else do
            idx <- findOp' rawOps
            pure `(There ~(idx))

findVar : FC ->
          SnocList String ->
          (nm : String) ->
          Elab TTImp
findVar fc [<] nm = failAt fc "Variable \{show nm} is not in context"
findVar fc (nms :< n) nm = if n == nm
    then pure `(Here)
    else do
        idx <- findVar fc nms nm
        pure `(There ~(idx))

export
term : Syntax s ->
       SnocList String ->
       TTImp ->
       Elab TTImp
term syn ctx = term' []
  where
    term' : (args : List TTImp) ->
            TTImp ->
            Elab TTImp
    term' args (IVar fc (UN (Basic nm))) = do
        case !(catch $ findOp fc syn nm) of
            Nothing => asVar
            Just opT => asOp opT
      where
        asOp : (opT : TTImp) -> Elab TTImp
        asOp opT = do
            op <- check {expected = Op syn} opT

            if length op.arity == length args
               then pure ()
               else failAt fc "Operation \{show op.name} has arity \{show $ length op.arity}, given \{show $ length args} arg(s)"

            pure `(Operation ~(opT) ~(impEnv op.index) ~(snocListLit args))

        asVar : Elab TTImp
        asVar = do
            varT <- findVar fc ctx nm

            case args of
                [] => pure ()
                _ :: _ => failAt fc "Variable \{show nm} is not a function"

            pure `(Var ~(varT))
    term' args (IApp fc f x) = do
        arg <- term' [] x
        term' (arg :: args) f
    term' args h@(IHole _ _) = pure h
    term' args t = failAt (getFC t) "Language does not support this construct"

%macro
export
fromTTImp : {syn : Syntax s} ->
            {ctx : Context s} ->
            TTImp ->
            Elab (Term syn ctx a)
fromTTImp t = term syn (map fst ctx) t >>= check
