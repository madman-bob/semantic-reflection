module SemanticReflectionTests

import Test.Golden

main : IO ()
main = runner [
    !(testsInDir "SingleSorted" (const True) "Single Sorted" [] Nothing),
    !(testsInDir "SingleSorted/Property" (const True) "Single Sorted Property" [] Nothing),
    !(testsInDir "Example" (const True) "Examples" [] Nothing)
  ]
