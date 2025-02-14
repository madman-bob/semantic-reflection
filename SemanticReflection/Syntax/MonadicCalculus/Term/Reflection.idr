module Syntax.MonadicCalculus.Term.Reflection

import public Language.Reflection

import public Syntax.MonadicCalculus.Syntax
import public Syntax.MonadicCalculus.Term.Base

%default total

export
term : Syntax t -> TTImp -> Elab TTImp
term syn (IVar fc (UN (Basic nm))) = do
    let nm' = IPrimVal fc $ Str nm
    let search = mapTopmostFC (const fc) `(%search)

    pure $ if elem nm $ map fst syn.primitives
        then `(PrimApp {nm = ~(nm')} ~(search) MkUnit)
        else `(Var $ forgetName {nm = ~(nm')} ~(search))
term syn `(()) = do
    pure `(MkUnit)
term syn (IAlternative _ (UniqueDefault `(~(IVar _ `{Builtin.MkPair}) ~(x) ~(y))) _) = do
    x <- term syn x
    y <- term syn y
    pure `(MkPair ~(x) ~(y))
term syn `(fst ~(x)) = do
    x <- term syn x
    pure `(Fst ~(x))
term syn `(snd ~(x)) = do
    x <- term syn x
    pure `(Snd ~(x))
term syn `(pure ~(x)) = do
    x <- term syn x
    pure `(Pure ~(x))
term syn `((>>=) ~(val) ~(ILam fc MW ExplicitArg (Just (UN (Basic nm))) ty body)) = do
    let nm = IPrimVal fc $ Str nm
    val <- term syn val
    body <- term syn body
    pure `(Bind ~(nm) ~(val) ~(body))
term syn `((>>) ~(val) ~(body)) = do
    val <- term syn val
    body <- term syn body
    pure `(Bind "" ~(val) ~(body))
term syn `(~(IVar fc (UN (Basic p))) ~(x)) = do
    let p = IPrimVal fc $ Str p
    x <- term syn x
    pure `(PrimApp {nm = ~(p)} %search ~(x))
term syn (ILet _ fc MW (UN (Basic nm)) ty val body) = do
    let nm = IPrimVal fc $ Str nm
    val <- term syn val
    body <- term syn body
    pure `(Let ~(nm) ~(val) ~(body))
term syn h@(IHole _ _) = pure h
term syn t = failAt (getFC t) "Language does not support this construct"

%macro
export
fromTTImp : {syn : Syntax t} -> TTImp -> Elab (Term syn ctx a)
fromTTImp t = check !(term syn t)
