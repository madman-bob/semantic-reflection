module SemanticReflectionTests

import Test.Golden

main : IO ()
main = runner [
    !(testsInDir "SingleSorted" "Single Sorted"),
    !(testsInDir "SingleSorted/Property" "Single Sorted Property"),
    !(testsInDir "ManySorted" "Many Sorted"),
    !(testsInDir "Example" "Examples")
  ]
