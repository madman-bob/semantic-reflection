module Syntax.ManySorted.Term.Reflection

import public Language.Reflection

import public Syntax.ManySorted.Interpretation
import public Syntax.ManySorted.Syntax
import public Syntax.ManySorted.Term.Base

%default total

||| Require two potentially unknown values to unify
unify : (0 x : a) -> (0 y : a) -> Elab (x = y)
unify x y = check $ ISearch EmptyFC 50

||| An implicit environment for a known context
|||
||| All values in the environment are implicit, and must be forced by use
impEnv : {ctx : Context s} -> Elab (Env ctx u)
impEnv {ctx = [<]} = pure [<]
impEnv {ctx = ctx :< (nm, a)} = [| impEnv {ctx} :< check (Implicit EmptyFC False) |]

lookupName : {default EmptyFC fc : FC} ->
             {ctx : Context s} ->
             (nm : String) ->
             Env ctx u ->
             Elab TTImp
lookupName {ctx = [<]} nm [<] = failAt fc "Variable \{show nm} is not in context"
lookupName {ctx = ctx :< (n, a)} nm (env :< x) =
    if n == nm
        then quote x
        else lookupName {fc} nm env

export
term : {syn : Syntax s} ->
       {ctx : Context s} ->
       TTImp ->
       Elab (Term syn ctx a)
term = term' []
  where
    term' : {0 a : s} ->
            (args : List TTImp) ->
            TTImp ->
            Elab (Term syn ctx a)
    term' {a} args (IVar fc (UN (Basic nm))) = case findOp {syn} nm of
        Just op => asOp op
        Nothing => asVar
      where
        collectArgs : {c : Context s} ->
                      (args : SnocList TTImp) ->
                      Elab (Env c (Term syn ctx))
        collectArgs {c = [<]} [<] = pure [<]
        collectArgs {c = c :< (nm, a)} (args :< arg) =
            [| collectArgs args :< assert_total (term' [] arg) |]
        collectArgs _ = failAt fc "Incorrect number of arguments"

        asOp : Op syn ->
               Elab (Term syn ctx a)
        asOp op = do
            i <- impEnv
            resultCorrect <- unify (op.result i) a

            if length op.arity == length args
               then pure ()
               else failAt fc "Operation \{show op.name} has arity \{show $ length op.arity}, given \{show $ length args} arg(s)"

            args <- collectArgs $ cast args
            pure $ replace {p = Term syn ctx} resultCorrect $ Operation op i args

        asVar : Elab (Term syn ctx a)
        asVar = do
            var <- ctxHack !(lookupName {fc} nm $ varEnv {syn} {ctx})

            case args of
                [] => pure ()
                _ :: _ => failAt fc "Variable \{show nm} is not a function"

            check var
          where
            ||| For some reason, quoting varEnv results in ?ctx holes where the context should be.
            ||| If we have multiple variables, this results in a "ctx is already defined" error.
            ||| The `id` trick doesn't seem to work here.
            ||| This hack works around this issue.
            ||| Maybe related to Idris issue #2993
            ctxHack : TTImp -> Elab TTImp
            ctxHack = mapMTTImp $ \case
                IHole fc "ctx" => quote ctx
                t => pure t

    term' args (IApp fc f x) = term' (x :: args) f
    term' args h@(IHole _ _) = check h
    term' args t = failAt (getFC t) "Language does not support this construct"

%macro
export
fromTTImp : {syn : Syntax s} ->
            {ctx : Context s} ->
            TTImp ->
            Elab (Term syn ctx a)
fromTTImp t = term t
