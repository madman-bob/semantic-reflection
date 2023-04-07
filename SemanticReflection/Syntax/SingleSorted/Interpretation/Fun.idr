module Syntax.SingleSorted.Interpretation.Fun

import public Syntax.SingleSorted.Interpretation.Env

%default total

||| A generalized interpretation of an operation in a context and type a, to type b
|||
||| A generalized interpretation can be viewed as an interpretation of an operation
||| in a context and type a, composed with a regular Idris function of type a -> b.
|||
||| This is a useful intermediate representation for an operation that has been
||| partially interpreted as an Idris function.
public export
Fun' : (ctx : Context) -> (a : Type) -> (b : Type) -> Type
Fun' [<] a b = b
Fun' (ctx :< _) a b = Fun' ctx a (a -> b)

||| An interpretation of an operation in a context, of type a
public export
Fun : (ctx : Context) -> (a : Type) -> Type
Fun ctx a = Fun' ctx a a

public export
curry : {ctx : Context} ->
        (Env ctx a -> b) ->
        Fun' ctx a b
curry {ctx = [<]} f = f [<]
curry {ctx = ctx :< _} f = curry {ctx} (f .: (:<))

public export
uncurry : Fun' ctx a b -> Env ctx a -> b
uncurry f [<] = f
uncurry {ctx = ctx :< _} f (xs :< x) = uncurry f xs x
