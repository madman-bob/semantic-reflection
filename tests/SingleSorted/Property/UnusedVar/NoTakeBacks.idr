import Syntax.SingleSorted.Property.UnusedVar.NoTakeBacks

import Language.Monoid

%default total

%language ElabReflection

%hint
monoidNoTakeBacks : NoTakeBacks MonoidThy
monoidNoTakeBacks = [<
    MkNoTakeBacks
        [<
            There (There Here) Here,
            There Here $ There (There Here) Here,
            There Here $ There Here Here
        ] [<
            There (There Here) $ There (There Here) Here,
            There (There Here) $ There Here Here,
            There Here Here
        ],
    MkNoTakeBacks [<There Here Here] [<Here],
    MkNoTakeBacks [<There (There Here) Here] [<Here]
  ]

someTerm : Term MonoidSyn [<"x", "y", "z"]
someTerm = `((x * y) * (e * x))
