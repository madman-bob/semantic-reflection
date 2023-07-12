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
Fun' : (ctx : Context) -> (a : Type) -> (b : Env ctx a -> Type) -> Type
Fun' [<] a b = b [<]
Fun' (ctx :< _) a b = Fun' ctx a $ \env => (x : a) -> b (env :< x)

||| An interpretation of an operation in a context, of type a
public export
Fun : (ctx : Context) -> (a : Type) -> Type
Fun ctx a = Fun' ctx a (const a)

public export
curry : {ctx : Context} ->
        {0 b : Env ctx a -> Type} ->
        ((env : Env ctx a) -> b env) ->
        Fun' ctx a b
curry {ctx = [<]} f = f [<]
curry {ctx = ctx :< _} f = curry {ctx} $ \env, x => f (env :< x)

public export
uncurry : Fun' ctx a b -> (env : Env ctx a) -> b env
uncurry f [<] = f
uncurry f (env :< x) = (the ((x : a) -> b (env :< x)) $ uncurry f env) x

export
uncurryCurry : {0 b : Env ctx a -> Type} ->
               {0 f : (env : Env ctx a) -> b env} ->
               uncurry {b} (curry f) env = f env
uncurryCurry = irrelevantEq uncurryCurry'
  where
    uncurryCurry' : {0 ctx : Context} ->
                    {0 b : Env ctx a -> Type} ->
                    {0 f : (env : Env ctx a) -> b env} ->
                    {env : Env ctx a} ->
                    uncurry {b} (curry f) env = f env
    uncurryCurry' {ctx = [<]} {env = [<]} = Refl
    uncurryCurry' {ctx = ctx :< nm} {b} {f} {env = env :< x} = cong (\g => g x) $ uncurryCurry' {ctx} {b = \env => (x : a) -> b (env :< x)} {f = \env, x => f (env :< x)} {env}
