import Data.List
import Data.Nat

import Syntax.SingleSorted.Model

%default total

%language ElabReflection

MonoidSyn : Syntax
MonoidSyn = `(\case e => 0; (*) => 2)

%runElab openSyn `{MonoidSyn}
%hide Prelude.(*)

MonoidThy : Theory MonoidSyn
MonoidThy = `([<
    x * (y * z) = (x * y) * z,
    e * x = x,
    x * e = x
  ])

Model MonoidThy (List a) where
    int = MkInterp `(\case
        e => []
        (*) => (++)
    )

    satThy = [<
        Prf appendAssociative,
        Prf \xs => Refl,
        Prf appendNilRightNeutral
    ]

Model MonoidThy Nat where
    int = MkInterp `(\case
        e => 0
        (*) => (+)
    )

    satThy = [<
        Prf plusAssociative,
        Prf plusZeroLeftNeutral,
        Prf plusZeroRightNeutral
    ]

eg : Term MonoidSyn [<"x", "y"]
eg = `(x * y)

listAssoc : (x : List a) ->
            (y : List a) ->
            (z : List a) ->
            x ++ (y ++ z) = (x ++ y) ++ z
listAssoc = getPrf {a = List a} $ There (There Here)

someEquiv : Elem "x" ctx =>
            Elem "y" ctx =>
            Equiv MonoidThy {ctx} `((e * x) * (y * e)) `(x * y)
someEquiv = SomeEquiv
  where
    L : Term MonoidSyn ctx
    L = `((e * x) * (y * e))

    R : Term MonoidSyn ctx
    R = `(x * y)

    [SomeEquiv] Equiv MonoidThy L R where
        isEquiv {a} env = irrelevantEq $ cong2 (*) (getPrf {a} (There Here) _) (getPrf {a} Here _)

nxe : Elem "x" ctx => Not (Equiv MonoidThy {ctx} `(x) `(e))
nxe (IsEquiv isEquiv) = absurd $ trans (sym constEnvConst) $ isEquiv {a = Nat} (constEnv 1)

namespace IsE
    export
    data IsE : Term MonoidSyn ctx -> Type where
        LitE : IsE `(e)
        EProd : IsE l -> IsE r -> IsE {ctx} (l * r)

    isEZero : {t : Term MonoidSyn ctx} -> IsE t -> evalEnv {a = Nat} (constEnv 1) t = 0
    isEZero {t = Operation (MkOp (There Here)) [<]} LitE = Refl
    isEZero {t = Operation (MkOp Here) [<l, r]} (EProd le re) = cong2 (+) (isEZero le) (isEZero re)

    zeroIsE : {t : Term MonoidSyn ctx} -> (0 prf : evalEnv {a = Nat} (constEnv 1) t = 0) -> IsE t
    zeroIsE {t = Var idx} prf = absurd $ trans (sym prf) constEnvConst
    zeroIsE {t = Operation (MkOp Here) [<l, r]} prf = do
        EProd (zeroIsE $ sumZeroL prf) (zeroIsE $ sumZeroR prf)
      where
        sumZeroL : {x : Nat} -> x + y = 0 -> x = 0
        sumZeroL {x = 0} prf = Refl
        sumZeroL {x = S _} prf = absurd prf

        sumZeroR : {x : Nat} -> x + y = 0 -> y = 0
        sumZeroR {x = 0} prf = prf
        sumZeroR {x = S _} prf = absurd prf
    zeroIsE {t = Operation (MkOp (There Here)) [<]} prf = LitE

    export
    Property MonoidThy IsE where
        replace (IsEquiv isEquiv) isE = zeroIsE $ trans (sym $ isEquiv _) (isEZero isE)

    export
    isE : {ctx : Context} ->
          (t : Term MonoidSyn ctx) ->
          Dec (IsE t)
    isE t with (evalEnv {a = Nat} (constEnv 1) t) proof prf
      _ | 0 = Yes $ zeroIsE prf
      _ | S _ = No $ \isE => absurd $ trans (sym prf) (isEZero isE)
