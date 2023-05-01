# Semantic Reflection

Reinterpreting Idris syntax in multiple contexts.

For example, the function `\x => 2 * x` could mean:

- An ordinary [Idris function](https://github.com/idris-lang/Idris2)
- A [mathematical function](https://en.wikipedia.org/wiki/Function_(mathematics))
- A [differentiable function](https://en.wikipedia.org/wiki/Differentiable_function)
- A function that produces [dynamically recomputing values](https://en.wikipedia.org/wiki/Incremental_computing), that change whenever its argument is changed.

Each of these has subtleties.

- Idris functions have compile-time and runtime behaviours to consider.
- Mathematical functions [don't](https://en.wikipedia.org/wiki/Extensionality) have compile-time and runtime behaviours to consider.
- Differentiable functions have a derivative, which satisfies certain laws.
- Recomputing values need to keep track of when and how to update values.

## Example

Here is an example implementation of [monoid theory](https://en.wikipedia.org/wiki/Monoid).

First we define the syntax of monoids

```idris
import Data.List
import Syntax.SingleSorted

%default total
%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)
```

Monoids are an example of single-sorted syntax, so we are using `Syntax.SingleSorted`. We import `Data.List` as we will later implement an example model on `List`s.

The backtick `` ` `` in the definition of `MonoidSyn` indicates that we are reinterpreting the standard Idris syntax to mean something else. Precisely how we are interpreting it depends on the type of what we are attempting to interpret it as. In the case of `Syntax`, we must use a `\case` block, which represents the different operations in a syntax. This implicitly creates the operations named on the LHS of the `=>`s, with the arities given on the RHS.

The `*` is defined as an infix operator, as we are using the standard Idris precedence rules.

We can now write terms in this syntax.

```idris
eg : Term MonoidSyn [<"x", "y"]
eg = `(x * (e * y) * x)
```

This time, the `` ` `` interprets Idris syntax to mean a term in the syntax we have just defined, with free variables `x` and `y`. We can *only* use these variables within a `Term` - in this context, outside Idris variables don't exist.

To evaluate terms semantically, we first have to define our semantics. In this case, we are using the standard monoid axioms.

```idris
MonoidThy : Theory MonoidSyn
MonoidThy = `([<
    x * (y * z) = (x * y) * z,
    e * x = x,
    x * e = x
  ])
```

For ease of implementation, we only support [equational axioms](https://en.wikipedia.org/wiki/Variety_(universal_algebra)).

We can use `` ` `` notation for both individual axioms, and whole theories. For example, `` the (Axiom MonoidSyn) `(e * x = x) ``. Using axiom `` ` `` notation implicitly quantifies over all used variables. In the above theory, the first axiom binds variables `x`, `y`, and `z`, while the other two axioms bind only `x`.

We can now define a model of this theory.

```idris
Model MonoidThy (List a) where
    int = MkInterp `(\case e => []; (*) => (++))

    satThy = [<
        Prf appendAssociative,
        Prf \xs => Refl,
        Prf appendNilRightNeutral
    ]
```

First we define an interpretation of the syntax `int`, and then we prove that this interpretation satisfies the theory with `satThy`.

We are using the `` ` `` in the interpretation to do a case split on the operations of the syntax. The RHS of these `=>`s are interpreted with standard Idris semantics. The arities of the operations are enforced, with `e` mapping to a constant, and `*` to a binary operation, both on `List a`.

The proofs that this interpretation satisfies the monoid laws are standard Idris proofs. We use `appendAssociative` and `appendNilRightNeutral` from `Data.List`.

We can now evaluate terms in this model.

```idris
result : List Nat
result = eval eg [1, 2] [3, 4]
```

Recall ``eg = `(x * (e * y) * x)``, so this gives `result = [1, 2, 3, 4, 1, 2]`.

For more example theories, see [SemanticReflection/Language](SemanticReflection/Language).

For example models of these theories, see [SemanticReflection/Data](SemanticReflection/Data).