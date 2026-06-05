module Syntax.SingleSorted.Term.Reflection

import public Syntax.SingleSorted.Env
import public Syntax.SingleSorted.Syntax
import public Syntax.SingleSorted.Term.Base

%default total

export
term : (syn : Syntax) ->
       TTImp ->
       Elab TTImp
term syn h@(IHole _ _) = pure h
term syn s = do
    let (s, args) = collectArgs s []

    (fc, nm) : (FC, String) <- case s of
        IVar fc (UN (Basic nm)) => pure (fc, nm)
        IBindVar fc (UN (Basic nm)) => pure (fc, nm)
        _ => failAt (getFC s) "Language does not support this construct"

    case find ((== nm) . name) syn.rawOps of
        Nothing => case args of
            [] => do
                let nm = IPrimVal fc $ Str nm
                let search = mapTopmostFC (const fc) `(%search)
                pure `(Var {v = ~(nm)} ~(search))
            _ :: _ => failAt fc "Variable \{show nm} is not a function"
        Just rawOp => if length args == rawOp.arity
            then do
                op <- operation syn s
                args <- assert_total $ traverse (term syn) args
                pure `(Operation ~(op) ~(snocListLit args))
            else failAt fc "Operation has arity \{show rawOp.arity}, given \{show $ length args} args"
  where
    collectArgs : TTImp -> List TTImp -> (TTImp, List TTImp)
    collectArgs (IApp _ f x) acc = collectArgs f (x :: acc)
    collectArgs s acc = (s, acc)

%macro
export
fromTTImp : {syn : Syntax} -> TTImp -> Elab (Term syn ctx)
fromTTImp s = check !(term syn s)
