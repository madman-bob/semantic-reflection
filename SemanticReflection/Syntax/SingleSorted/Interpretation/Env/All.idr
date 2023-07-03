module Syntax.SingleSorted.Interpretation.Env.All

import public Syntax.SingleSorted.Interpretation.Env

%default total

public export
data AllVars : (0 ctx : Context) -> (0 p : forall nm. Elem nm ctx -> Type) -> Type where
    Lin : {0 p : forall nm. Elem nm [<] -> Type} ->
          AllVars [<] p
    (:<) : {0 p : forall n. Elem n (ctx :< m) -> Type} ->
           AllVars ctx (p . There) -> p Here -> AllVars (ctx :< m) p

%name AllVars pvs

public export
All : (env : Env ctx a) -> (p : a -> Type) -> Type
All env p = AllVars ctx $ \idx => p (get env idx)

public export
allVars : {ctx : Context} ->
          {0 p : forall nm. Elem nm ctx -> Type} ->
          ({0 nm : String} -> (idx : Elem nm ctx) -> p idx) ->
          AllVars ctx p
allVars {ctx = [<]} f = [<]
allVars {ctx = ctx :< nm} f = allVars {ctx} (\idx => f $ There idx) :< f Here

public export
allVars' : (env : Env ctx a) ->
           {0 p : forall nm. Elem nm ctx -> Type} ->
           ({0 nm : String} -> (idx : Elem nm ctx) -> p idx) ->
           AllVars ctx p
allVars' [<] f = [<]
allVars' (env :< x) f = allVars' env (\idx => f $ There idx) :< f Here

public export
getAll : {0 p : forall nm. Elem nm ctx -> Type} ->
         AllVars ctx p ->
         (idx : Elem nm ctx) ->
         p idx
getAll (pvs :< pv) Here = pv
getAll (pvs :< _) (There idx) = getAll pvs idx

public export
mapAllVars : {0 p : forall nm. Elem nm ctx -> Type} ->
             {0 q : forall nm. Elem nm ctx -> Type} ->
             ({0 nm : String} -> {0 idx : Elem nm ctx} -> p idx -> q idx) ->
             AllVars ctx p ->
             AllVars ctx q
mapAllVars f [<] = [<]
mapAllVars f (pvs :< pv) = mapAllVars f pvs :< f pv

public export
mapAll : ({0 x : a} -> p x -> q x) ->
         All env p ->
         All env q
mapAll f pvs = mapAllVars f pvs
