import Syntax.SingleSorted.Property.UnusedVar.Syntactic

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

xInvxUsed : {0 i : Elem nm ctx} ->
            SynUsedVar {syn = GroupSyn} i (Var i * inv (Var i))
xInvxUsed = There (There Here) Here

eUnused : {0 i : Elem nm ctx} ->
          Not (SynUsedVar {syn = GroupSyn} i `(e))
eUnused (There pos posUsed) = absurd pos

eSemUnused : UnusedVar GroupThy i `(e)
eSemUnused = synUnusedUnused eUnused

xInvxEquive : {0 i : Elem nm ctx} ->
              Equiv GroupThy (Var i * inv (Var i)) `(e)
xInvxEquive = IsEquiv $ \env => rightInv (get env i)

synUseNotSemProperty : {0 i : Elem nm ctx} ->
                       Not (Property GroupThy (SynUsedVar i))
synUseNotSemProperty isProperty = void $ eUnused eUsed
  where
    0
    eUsed : SynUsedVar {syn = GroupSyn} i `(e)
    eUsed = replace @{isProperty} xInvxEquive xInvxUsed
