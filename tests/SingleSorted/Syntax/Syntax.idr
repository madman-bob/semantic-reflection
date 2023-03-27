import Syntax.SingleSorted.Syntax

%default total

multOp : RawOp
multOp = MkRawOp "*" 2

MonoidSyn : Syntax
MonoidSyn = MkSyntax [<MkRawOp "e" 0, multOp]

monoidMult : Op MonoidSyn
monoidMult = MkOp Here

%language ElabReflection

GroupSyn : Syntax
GroupSyn = `(\case e => 0; (*) => 2; inv => 1)

groupMult : Op GroupSyn
groupMult = `((*))
