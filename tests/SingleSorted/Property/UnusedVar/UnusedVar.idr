import Data.Bool.Xor

import Syntax.PreorderReasoning

import Syntax.SingleSorted.Property.UnusedVar

%default total

%language ElabReflection

GroupSyn : Syntax
GroupSyn = `(\case e => 0; (*) => 2; inv => 1)

GroupThy : Theory GroupSyn
GroupThy = `[
    assoc : x * (y * z) = (x * y) * z
    leftId : e * x = x
    rightId : x * e = x
    leftInv : inv x * x = e
    rightInv : x * inv x = e
  ]

%runElab openSyn `{GroupSyn}
%runElab openThy `{GroupThy}
%hide Prelude.(*)

unusedInE : {0 i : Elem v ctx} ->
            UnusedVar GroupThy i `(e)
unusedInE = IsUnused $ \env, x => Refl

unusedInXInvX : {0 i : Elem "x" ctx} ->
                UnusedVar GroupThy i `(x * inv x)
unusedInXInvX = IsUnused $ \env, x => Calc $
    |~ evalEnv env `(x * inv x)
    ~~ e                                       ...(rightInv _)
    ~~ evalEnv (replace env i x) `(x * inv x)  ..<(rightInv _)

sameType : (0 x : a) -> (0 y : b) -> x = y -> a = b
sameType x x Refl = Refl

unusedComplex : {i : Elem "x" ctx} ->
                {j : Elem "y" ctx} ->
                {k : Elem "z" ctx} ->
                UnusedVar GroupThy i `((y * x) * (inv x * z))
unusedComplex = Property.replace {thy = GroupThy} (symmetric equiv) $
    IsUnused $ \env, x => sym $ cong2 (*)
        (replaceDiff $ (\case Refl impossible) . (sameType i j))
        (replaceDiff $ (\case Refl impossible) . (sameType i k))
  where
    equiv : Equiv GroupThy {ctx} `((y * x) * (inv x * z)) `(y * z)
    equiv = IsEquiv $ \env => Calc $
            |~ evalEnv env `((y * x) * (inv x * z))
            ~~ evalEnv env `(((y * x) * inv x) * z) ...(assoc _ _ _)
            ~~ evalEnv env `((y * (x * inv x)) * z) ...(cong (flip (*) _) $ sym $ assoc _ _ _)
            ~~ evalEnv env `((y * e) * z)           ...(cong (\w => (get env j * w) * get env k) $ rightInv _)
            ~~ evalEnv env `(y * z)                 ...(cong (flip (*) _) $ rightId _)

Model GroupThy Bool where
    int = MkInterp `(\case
        e => False
        (*) => xor
        inv => id
    )

    satThy = [<
        Prf xorAssociative,
        Prf xorFalseNeutral,
        Prf $ \x => trans (xorCommutative _ _) $ xorFalseNeutral x,
        Prf xorSameFalse,
        Prf xorSameFalse
    ]

usedInX : {0 i : Elem "x" ctx} ->
          Not (UnusedVar GroupThy i `(x))
usedInX xUnused = absurd $ irrelevantEq $ Calc $
    |~ False
    ~~ get (constEnv False) i                  ..<(constEnvConst)
    ~~ get (replace (constEnv False) i True) i ...(xUnused.canReplace _ _)
    ~~ True                                    ...(replaceSame)

usedComplex : {0 i : Elem "x" ctx} ->
              {0 j : Elem "y" ctx} ->
              {0 k : Elem "z" ctx} ->
              Not (UnusedVar GroupThy i `(y * inv x * z))
usedComplex xUnused = absurd $ irrelevantEq $ Calc $
    |~ False
    ~~ evalEnv (constEnv False) `(y * inv x * z)
        ..<(cong2 xor (cong2 xor constEnvConst constEnvConst) constEnvConst)
    ~~ evalEnv (replace (constEnv False) i True) `(y * inv x * z)
        ...(xUnused.canReplace _ _)
    ~~ True
        ...(cong2 xor (cong2 xor (otherFalse nyx) replaceSame) (otherFalse nzx))
  where
    otherFalse : {0 j : Elem nm ctx} -> Not (nm = "x") -> get (replace (constEnv False) i True) j = False
    otherFalse {j} notX = Calc $
        |~ get (replace (constEnv False) i True) j
        ~~ get (constEnv False) j                  ...(replaceDiff $ (\Refl => notX Refl) . sameType i j)
        ~~ False                                   ...(constEnvConst)

    nyx : Not ("y" = "x")
    nyx Refl impossible

    nzx : Not ("z" = "x")
    nzx Refl impossible

namespace ConstantThy
    ConstantSyn : Syntax
    ConstantSyn = `(\case e => 0)

    ConstantThy : Theory ConstantSyn
    ConstantThy = `[constant : x = e]

    %runElab openSyn `{ConstantSyn}
    %runElab openThy `{ConstantThy}

    alwaysUnused : {t : Term ConstantSyn ctx} ->
                   UnusedVar ConstantThy idx t
    alwaysUnused {t = Var i} = IsUnused $ \env, x => Calc $
        |~ get env i
        ~~ e                         ...(constant _)
        ~~ get (replace env idx x) i ..<(constant _)
    alwaysUnused {t = Operation (MkOp Here) [<]} = IsUnused $ \env, x => Refl

    constantThyConstant : Model ConstantThy a =>
                          {0 x : a} ->
                          {0 y : a} ->
                          x = y
    constantThyConstant = unusedInSelf {ctx = [<"x"]} Here alwaysUnused
