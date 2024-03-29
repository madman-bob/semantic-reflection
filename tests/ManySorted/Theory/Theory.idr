import Data.Vect

import Syntax.ManySorted.Theory

%default total

%language ElabReflection

SizedMonoidSyn : Syntax Nat
SizedMonoidSyn = `[
    e : 0
    (*) : n -> m -> n + m
  ]

[ConcatInterp] Interp SizedMonoidSyn (\n => Vect n a) where
    impl = `(\case
        e => []
        x * y => x ++ y
    )

leftId : Axiom SizedMonoidSyn
leftId = do
    let
        MetaVars : Context Type
        MetaVars = [<"n" :! Nat]

        lhsSort : ISort MetaVars Nat
        lhsSort = \[<n] => n

        rhsSort : ISort MetaVars Nat
        rhsSort = \[<n] => n
    MkAxiom
        "leftId"
        MetaVars
        [<"x" :! \[<n] => n]
        {lhsSort}
        (\[<n] => `(e * x))
        {rhsSort}
        (\[<n] => `(x))

leftId' : Axiom SizedMonoidSyn
leftId' = `[leftId : {x : n} -> e * x = x]

leftIdsEq : Main.leftId = Main.leftId'
leftIdsEq = Refl

leftId'' : Axiom SizedMonoidSyn
leftId'' = `[leftId : e * x = x]

failing "Expected axiom"
    badAx : Axiom SizedMonoidSyn
    badAx = `[leftId : e * x]

failing "Expected single axiom"
    badAx : Axiom SizedMonoidSyn
    badAx = `[leftId : e * x = x; rightId : x * e = x]

SizedMonoidThy : Theory SizedMonoidSyn
SizedMonoidThy = [<
    `[assoc : {x : n} -> {y : m} -> {z : p} -> x * (y * z) = (x * y) * z],
    leftId,
    `[rightId : {x : n} -> x * e = x]
  ]

SizedMonoidThy' : Theory SizedMonoidSyn
SizedMonoidThy' = `[
    assoc : {x : n} -> {y : m} -> {z : p} -> x * (y * z) = (x * y) * z
    leftId : {x : n} -> e * x = x
    rightId : {x : n} -> x * e = x
  ]

SizedMonoidThysEq : SizedMonoidThy = SizedMonoidThy'
SizedMonoidThysEq = Refl

[ConcatLeftId] SatAxiom ConcatInterp Main.leftId where
    prf [<n] [<x] = Refl

ConcatSatSizedMonoidThy : SatTheory ConcatInterp SizedMonoidThy
ConcatSatSizedMonoidThy = [<
    MkSatAxiom $ \[<n, m, p], [<x, y, z] => vectAppendAssociative,
    ConcatLeftId,
    MkSatAxiom $ \[<n], [<x] => vectAppendNilRightNeutral
  ]
  where
    typesEq : {0 x : a} -> {0 y : b} -> (0 prf : x ~=~ y) -> a = b
    typesEq Refl = Refl

    hcong : (0 p : a -> Type) ->
            (0 _ : Injective p) =>
            {0 q : a -> Type} ->
            (0 f : {i : a} -> p i -> q i) ->
            {0 x : p i} ->
            {0 y : p j} ->
            (0 prf : x ~=~ y) ->
            f x ~=~ f y
    hcong p f xy = do
        let pij = typesEq xy
        let Refl = irrelevantEq $ injective pij
        let Refl = irrelevantEq xy
        Refl

    vectAppendAssociative : {xs : Vect n a} -> {0 ys : Vect m a} -> {0 zs : Vect p a} -> xs ++ (ys ++ zs) ~=~ (xs ++ ys) ++ zs
    vectAppendAssociative {xs = []} = Refl
    vectAppendAssociative {xs = x :: xs} =
        hcong (\n => Vect n a) @{MkInjective $ \Refl => Refl} (x ::) $
        vectAppendAssociative {xs} {ys} {zs}

    vectAppendNilRightNeutral : {xs : Vect n a} -> xs ++ [] ~=~ xs
    vectAppendNilRightNeutral {xs = []} = Refl
    vectAppendNilRightNeutral {xs = x :: xs} =
        hcong (\n => Vect n a) @{MkInjective $ \Refl => Refl} (x ::) $
        vectAppendNilRightNeutral {xs}
