module Syntax.ManySorted.Syntax.Reflection

import public Control.Monad.State
import public Decidable.Equality

import public Language.Reflection

import public Syntax.ManySorted.Syntax.Base

%default total

namespace RawOp
    freeVars : TTImp -> SnocList String
    freeVars t = execState [<] $ mapMTTImp addVarName t
      where
        addVarName : TTImp -> State (SnocList String) TTImp
        addVarName t@(IBindVar _ nm) = do
            case isElem nm !get of
                Yes _ => pure ()
                No _ => modify (:< nm)
            pure t
        addVarName t = pure t

    export
    rawOp : Decl -> Elab (RawOp s)
    rawOp (IClaim $ MkFCVal fc $ MkIClaimData MW Private [] $ MkTy _ (MkFCVal _ $UN $ Basic nm) ty) = do
        let vars = freeVars ty
        index <- index vars
        (args, ret) <- sig vars ty

        pure $ MkRawOp nm index args ret
      where
        imp : TTImp
        imp = Implicit EmptyFC False

        index : SnocList String -> Elab (Context Type)
        index [<] = pure [<]
        index (nms :< nm) = [| index nms :< [| pure nm :! check imp |] |]

        sort : SnocList String ->
               TTImp ->
               Elab (Env i Prelude.id -> s)
        sort vars t = do
            let fc = getFC t

            let lin = IVar fc `{Syntax.ManySorted.Env.Lin}
            let snoc = \xs, x => IApp fc
                  (IApp fc
                      (IVar fc `{Syntax.ManySorted.Env.(:<)})
                      xs)
                  x

            let lhs = foldl snoc lin $ map (IBindVar fc) vars

            let rhs = flip mapTTImp t $ \case
                  IBindVar fc nm => IVar fc $ UN $ Basic nm
                  t => t

            idxNm <- genSym "idx"
            check $ ILam fc MW ExplicitArg (Just idxNm) imp
                (ICase fc [] (IVar fc idxNm) imp
                    [PatClause fc lhs rhs])

        sig : SnocList String ->
              TTImp ->
              Elab (List (Env i Prelude.id -> s), Env i Prelude.id -> s)
        sig vars (IPi fc MW ExplicitArg Nothing lhs rhs) = do
            arg <- sort vars lhs
            (args, ret) <- sig vars rhs
            pure (arg :: args, ret)
        sig vars (IPi fc _ _ _ _ _) = failAt fc "Expected unnamed explicit argument"
        sig vars t = do
            ret <- sort vars t
            pure ([], ret)
    rawOp decl = fail """
        Expected operator declaration
        eg.
          data ModuleSort = Matrix Nat Nat | Vector Nat

          ModuleSyn : Syntax ModuleSort
          ModuleSyn = `[
              I : Matrix n n
              (<+>) : Matrix n m -> Matrix n m -> Matrix n m
              (<*>) : Matrix n m -> Matrix m p -> Matrix n p
              (+) : Vector n -> Vector n -> Vector n
              (*) : Matrix n m -> Vector m -> Vector n
            ]
        """

    %macro
    export
    fromDecls : List Decl -> Elab (RawOp s)
    fromDecls [decl] = rawOp decl
    fromDecls decls = fail "Expected single operator declaration"

namespace Operation
    export
    opName : TTImp -> Elab String
    opName (IVar fc (UN (Basic nm))) = pure nm
    opName (IBindVar fc nm) = pure nm
    opName s = failAt (getFC s) "Expected operator"

    export
    operation : {syn : Syntax s} -> TTImp -> Elab (Op syn)
    operation t = do
        nm <- opName t
        let Just op = findOp nm
            | Nothing => failAt (getFC t) "Operator \{show nm} not in syntax"
        pure op

    %macro
    export
    fromTTImp : {syn : Syntax s} -> TTImp -> Elab (Op syn)
    fromTTImp t = operation t

namespace Syntax
    export
    syntax : List Decl -> Elab (Syntax s)
    syntax decls = do
        rawOps <- traverse (rawOp {s}) decls
        pure $ MkSyntax $ cast rawOps

    %macro
    export
    fromDecls : List Decl -> Elab (Syntax s)
    fromDecls t = syntax t
