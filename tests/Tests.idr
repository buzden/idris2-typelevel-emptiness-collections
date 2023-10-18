module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Musthave typechecks"           `atDir` "typechecks"
  , "Documentation"                 `atDir` "docs"
  , "Laziness of a list"            `atDir` "laziness"
  ]
