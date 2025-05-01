module Syntax.MonadicCalculus.Term.Base

import public Syntax.ManySorted.Env

import public Syntax.MonadicCalculus.Syntax
import public Syntax.MonadicCalculus.Type

%default total

public export
data Term : Syntax t -> Context (Ty t) -> Ty t -> Type where
    Var : {a : Ty t} -> Var ctx a -> Term {t} syn ctx a
    MkUnit : Term {t} syn ctx Unit
    MkPair : {a,b : Ty t} -> Term syn ctx a -> Term syn ctx b -> Term {t} syn ctx (Pair a b)
    Fst : {a,b : Ty t} -> Term syn ctx (Pair a b) -> Term {t} syn ctx a
    Snd : {a,b : Ty t} -> Term syn ctx (Pair a b) -> Term {t} syn ctx b
    PrimApp : {a,b : Ty t} -> NVar syn.primitives nm (MkPrimitive a b) -> Term syn ctx a -> Term {t} syn ctx b
    Let : {a,b : Ty t} -> (nm : String) -> Term syn ctx a -> Term syn (ctx :< (nm :! a)) b -> Term {t} syn ctx b
    Pure : {a : Ty t} -> Term syn ctx a -> Term syn ctx (T a)
    Bind : {a,b : Ty t} -> (nm : String) -> Term syn ctx (T a) -> Term syn (ctx :< (nm :! a)) (T b) -> Term {t} syn ctx (T b)
