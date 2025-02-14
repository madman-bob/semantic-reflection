module Syntax.MonadicCalculus.Term.Base

import public Syntax.ManySorted.Env

import public Syntax.MonadicCalculus.Syntax
import public Syntax.MonadicCalculus.Type

%default total

public export
data Term : Syntax t -> Context (Ty t) -> Ty t -> Type where
    Var : Var ctx a -> Term {t} syn ctx a
    MkUnit : Term {t} syn ctx Unit
    MkPair : Term syn ctx a -> Term syn ctx b -> Term {t} syn ctx (Pair a b)
    Fst : Term syn ctx (Pair a b) -> Term {t} syn ctx a
    Snd : Term syn ctx (Pair a b) -> Term {t} syn ctx b
    PrimApp : NVar syn.primitives nm (MkPrimitive a b) -> Term syn ctx a -> Term {t} syn ctx b
    Let : (nm : String) -> Term syn ctx a -> Term syn (ctx :< (nm :! a)) b -> Term {t} syn ctx b
    Pure : Term syn ctx a -> Term syn ctx (T a)
    Bind : (nm : String) -> Term syn ctx (T a) -> Term syn (ctx :< (nm :! a)) (T b) -> Term {t} syn ctx (T b)
