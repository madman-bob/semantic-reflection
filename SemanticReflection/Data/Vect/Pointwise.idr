module Data.Vect.Pointwise

import public Data.Vect

import Syntax.PreorderReasoning

import public Syntax.SingleSorted

%default total

transpose : {n : Nat} -> Env ctx (Vect n a) -> Vect n (Env ctx a)
transpose = sequence

envCons : Env ctx a -> Env ctx (Vect n a) -> Env ctx (Vect (S n) a)
envCons head tail = zipWith (::) head tail

transposeEnvCons : {head : Env ctx a} ->
                   {tail : Env ctx (Vect n a)} ->
                   transpose (envCons head tail) = head :: transpose tail
transposeEnvCons {head = [<]} {tail = [<]} = Refl
transposeEnvCons {head = head :< x} {tail = tail :< xs} = rewrite transposeEnvCons {head} {tail} in Refl

getEnvCons : {idx : Elem nm ctx} ->
             {head : Env ctx a} ->
             {tail : Env ctx (Vect n a)} ->
             get (envCons head tail) idx = get head idx :: get tail idx
getEnvCons {idx = Here} {head = head :< x} {tail = tail :< xs} = Refl
getEnvCons {idx = There idx} {head = head :< x} {tail = tail :< xs} = getEnvCons {idx}

public export
%hint
PointwiseInterp : {syn : Syntax} ->
                  Interp syn a =>
                  {n : Nat} ->
                  Interp syn (Vect n a)
PointwiseInterp {n} = MkInterp $ \op => curry {b = const $ Vect n a} $ \env => map (uncurry $ impl op) $ sequence env

pointwise : {syn : Syntax} ->
            Interp syn a =>
            {n : Nat} ->
            Env ctx (Vect n a) ->
            Term syn ctx ->
            Vect n a
pointwise = unsafeEvalEnv @{PointwiseInterp}

mutual
    pointwiseEnvCons : (0 _ : Interp syn a) =>
                       {t : Term syn ctx} ->
                       {0 head : Env ctx a} ->
                       {0 tail : Env ctx (Vect n a)} ->
                       pointwise (envCons head tail) t = unsafeEvalEnv head t :: pointwise tail t
    pointwiseEnvCons {t = Var idx} = irrelevantEq getEnvCons
    pointwiseEnvCons {t = Operation op args} = Calc $
        |~ pointwise (envCons head tail) (Operation op args)
        ~~ map (uncurry (impl op)) (transpose (map (pointwise (envCons head tail)) args))
            ...(uncurryCurry)
        ~~ map (uncurry (impl op)) (transpose (envCons (map (unsafeEvalEnv head) args) (map (pointwise tail) args)))
            ...(cong (map (uncurry (impl op)) . transpose) mapPointwiseEnvCons)
        ~~ uncurry (impl op) (map (unsafeEvalEnv head) args) :: map (uncurry (impl op)) (transpose (map (pointwise tail) args))
            ...(cong (map (uncurry (impl op))) transposeEnvCons)
        ~~ unsafeEvalEnv head (Operation op args) :: pointwise tail (Operation op args)
            ..<(cong2 Vect.(::) Refl uncurryCurry)

    mapPointwiseEnvCons : (0 _ : Interp syn a) =>
                          {0 vars : Context} ->
                          {ts : Env vars (Term syn ctx)} ->
                          {0 head : Env ctx a} ->
                          {0 tail : Env ctx (Vect n a)} ->
                          map (pointwise (envCons head tail)) ts = envCons (map (unsafeEvalEnv head) ts) (map (pointwise tail) ts)
    mapPointwiseEnvCons {ts = [<]} = Refl
    mapPointwiseEnvCons {ts = env :< x} = cong2 (:<) mapPointwiseEnvCons pointwiseEnvCons

envUncons : (env : Env ctx (Vect (S n) a)) ->
            (head : Env ctx a ** tail : Env ctx (Vect n a) ** envCons head tail = env)
envUncons [<] = ([<] ** [<] ** Refl)
envUncons (env :< (x :: xs)) = do
    let (head ** tail ** prf) = envUncons env
    (head :< x ** tail :< xs ** cong2 (:<) prf Refl)

pointwiseLiftEq : Interp syn a =>
                  {0 l : Term syn ctx} ->
                  {0 r : Term syn ctx} ->
                  (0 eq : (env : Env ctx a) -> unsafeEvalEnv env l = unsafeEvalEnv env r) ->
                  {n : Nat} ->
                  (env : Env ctx (Vect n a)) ->
                  pointwise env l = pointwise env r
pointwiseLiftEq eq {n = 0} env = vect0Eq
  where
    vect0Eq : {0 x : Vect 0 a} -> {0 y : Vect 0 a} -> x = y
    vect0Eq {x = []} {y = []} = Refl
pointwiseLiftEq eq {n = S n} env = do
    let (head ** tail ** prf) = envUncons env
    rewrite sym prf
    Calc $
        |~ pointwise (envCons head tail) l
        ~~ unsafeEvalEnv head l :: pointwise tail l ...(pointwiseEnvCons)
        ~~ unsafeEvalEnv head r :: pointwise tail r ...(cong2 (::) (eq head) (pointwiseLiftEq eq {n} tail))
        ~~ pointwise (envCons head tail) r          ..<(pointwiseEnvCons)

pointwiseSatAx : {0 int : Interp syn a} ->
                 {ax : Axiom syn} ->
                 (0 sat : SatAxiom int ax) ->
                 SatAxiom (PointwiseInterp @{int}) ax
pointwiseSatAx (Prf prf) = Prf $ curry {ctx = ax.vars} $ \env => irrelevantEq $ pointwiseLiftEq (uncurry prf) env

pointwiseSatThy : {0 int : Interp syn a} ->
                  {thy : Theory syn} ->
                  SatTheory int thy ->
                  SatTheory (PointwiseInterp @{int}) thy
pointwiseSatThy [<] = [<]
pointwiseSatThy (satThy :< sat) = pointwiseSatThy satThy :< pointwiseSatAx sat

public export
%hint
Pointwise : {syn : Syntax} ->
            {n : Nat} ->
            {thy : Theory syn} ->
            Model thy a =>
            Model thy (Vect n a)
Pointwise = MkModel PointwiseInterp (pointwiseSatThy satThy)
