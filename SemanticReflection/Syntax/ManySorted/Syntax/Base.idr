module Syntax.ManySorted.Syntax.Base

import Data.SnocList
import public Data.SnocList.Elem

import public Syntax.ManySorted.Env

%default total

||| A standalone operation, for a sort s
|||
||| An operation has a name, and its signature.
|||
||| An operation's signature is a list of the sorts it takes as arguments, and its
||| return sort.
|||
||| We define here an indexed collection of operations. This allows us to have
||| infinite collections of operations, with finite collections of names.
|||
||| For example, for graded monoids, our collection of sorts is a monoid.
||| A graded monoid has potentially infinitely-many composition operations.
||| For each pair of sorts x and y, we have a binary operation
|||   <*>_(x, y) : x -> y -> x * y
public export
record RawOp (s : Type) where
    constructor MkRawOp
    name : String
    index : Context Type
    arity : List (Env index Prelude.id -> s)
    result : Env index Prelude.id -> s

%name RawOp rawOp

||| A many-sorted syntax is defined by its signature:
||| - a collection of sorts
||| - a collection of operations
||| - for each operation, the signature of the operation
|||
||| For example, given a monoid `a`, we can define graded monoids over `a`.
||| Graded monoids have two classes of operations:
||| - The operation E, of signature e
||| - The operations <*>_(x, y), of signature x -> y -> x * y, for sorts x and y
public export
record Syntax (s : Type) where
    constructor MkSyntax
    rawOps : SnocList (RawOp s)

%name Syntax syn

||| An operation in a syntax
|||
||| The signature of the operation are determined by the syntax it is in
public export
record Op (syn : Syntax s) where
    constructor MkOp
    {0 rawOp : RawOp s}
    idx : Elem rawOp syn.rawOps

%name Op op

public export
name : {syn : Syntax s} ->
       Op syn ->
       String
name (MkOp idx) = name $ get syn.rawOps idx

public export
(.name) : {syn : Syntax s} ->
          Op syn ->
          String
(.name) = name

public export
index : {syn : Syntax s} ->
        Op syn ->
        Context Type
index (MkOp idx) = index $ get syn.rawOps idx

public export
(.index) : {syn : Syntax s} ->
           Op syn ->
           Context Type
(.index) = index

public export
arity : {syn : Syntax s} ->
        (op : Op syn) ->
        List (Env op.index Prelude.id -> s)
arity (MkOp idx) = arity $ get syn.rawOps idx

public export
(.arity) : {syn : Syntax s} ->
           (op : Op syn) ->
           List (Env op.index Prelude.id -> s)
(.arity) = arity

public export
result : {syn : Syntax s} ->
         (op : Op syn) ->
         Env op.index Prelude.id -> s
result (MkOp idx) = result $ get syn.rawOps idx

public export
(.result) : {syn : Syntax s} ->
            (op : Op syn) ->
            Env op.index Prelude.id -> s
(.result) = result

export
ops : (syn : Syntax s) ->
      SnocList (Op syn)
ops (MkSyntax [<]) = [<]
ops syn@(MkSyntax (rawOps :< rawOp)) =
    map
      (\(MkOp idx) => MkOp $ There idx)
      (ops (assert_smaller syn $ MkSyntax rawOps))
    :< MkOp Here

export
(.ops) : (syn : Syntax s) ->
         SnocList (Op syn)
(.ops) = ops

export
findOp : {syn : Syntax s} ->
         (name : String) ->
         Maybe (Op syn)
findOp name = find (\op => op.name == name) $ ops syn
