module Syntax.STLC.Term.Base

import public Syntax.STLC.Type

%default total

public export
data Term : Context (Ty t) -> Ty t -> Type where
    Var : Var ctx a -> Term {t} ctx a
    App : {a : Ty t} -> {b : Ty t} ->
          Term ctx (a ~> b) ->
          Term ctx a ->
          Term ctx b
    Lam : (nm : String) ->
          (a : Ty t) ->
          {b : Ty t} ->
          Term (ctx :< (nm :! a)) b ->
          Term ctx (a ~> b)

%name Term t
