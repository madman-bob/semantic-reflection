module Syntax.STLC.Term.Reflection

import public Language.Reflection

import public Syntax.STLC.Term.Base

%default total

export
term : TTImp -> Elab TTImp
term (IVar fc (UN (Basic nm))) = do
    let nm = IPrimVal fc $ Str nm
    let search = mapTopmostFC (const fc) `(%search)
    pure $ `(Var $ forgetName {nm = ~(nm)} ~(search))
term (IApp fc f x) = do
    f <- term f
    x <- term x
    pure $ mapTopmostFC (const fc) `(App ~(f) ~(x))
term (ILam fc MW ExplicitArg (Just (UN (Basic nm))) t body) = do
    let nm = IPrimVal fc $ Str nm
    t <- stlcType t
    body <- term body
    pure $ mapTopmostFC (const fc) `(Lam ~(nm) ~(t) ~(body))
term (ILet letFC varFC MW nm t val body) = do
    assert_total $
    term (IApp letFC (ILam letFC MW ExplicitArg (Just nm) t body) val)
term h@(IHole _ _) = pure h
term t = failAt (getFC t) "Language does not support this construct"

%macro
export
fromTTImp : TTImp -> Elab (Term {t} ctx a)
fromTTImp t = check !(term t)
