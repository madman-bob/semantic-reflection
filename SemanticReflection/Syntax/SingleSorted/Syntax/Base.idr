module Syntax.SingleSorted.Syntax.Base

import Data.SnocList
import public Data.SnocList.Elem

%default total

||| A standalone operation
|||
||| An operation has a name, and an arity - the number of arguments it takes
public export
record RawOp where
    constructor MkRawOp
    name : String
    arity : Nat

%name RawOp rawOp

public export
Show RawOp where
    show rawOp = "\{show rawOp.name} (arity \{show rawOp.arity})"

||| A single-sorted syntax is defined by its signature:
||| - a collection of operations
||| - for each operation, the arity of the operation - the number of arguments it takes
|||
||| For example, monoids have two operations, `e` and `*`.
||| - e, called the identity, is a constant, so has arity 0
||| - * is a binary operation, so has arity 2
||| So the signature of monoids is ({e, *}, {e -> 0, * -> 2})
public export
record Syntax where
    constructor MkSyntax
    rawOps : SnocList RawOp

%name Syntax syn

public export
Show Syntax where
    show syn = show syn.rawOps

||| An operation in a syntax
|||
||| The name and arity of the operation are determined by the syntax it is in
public export
record Op (syn : Syntax) where
    constructor MkOp
    idx : Elem rawOp syn.rawOps

%name Op op

public export
{syn : Syntax} -> Show (Op syn) where
    show (MkOp idx) = show $ get syn.rawOps idx

public export
name : {syn : Syntax} ->
       Op syn ->
       String
name (MkOp idx) = name $ get syn.rawOps idx

public export
(.name) : {syn : Syntax} ->
          Op syn ->
          String
(.name) = name

public export
arity : {syn : Syntax} ->
        Op syn ->
        Nat
arity (MkOp idx) = arity $ get syn.rawOps idx

public export
(.arity) : {syn : Syntax} ->
           Op syn ->
           Nat
(.arity) = arity

public export
ops : (syn : Syntax) ->
      SnocList (Op syn)
ops (MkSyntax [<]) = [<]
ops syn@(MkSyntax (rawOps :< rawOp)) = map (\(MkOp idx) => MkOp $ There idx) (ops $ assert_smaller syn (MkSyntax rawOps)) :< MkOp Here

public export
(.ops) : (syn : Syntax) ->
         SnocList (Op syn)
(.ops) = ops

export
findOp : {syn : Syntax} ->
         (name : String) ->
         Maybe (Op syn)
findOp name = find (\op => op.name == name) $ ops syn
