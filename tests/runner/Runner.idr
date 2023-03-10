module Runner

import BaseDir

import Test.Golden.RunnerHelper

RunScriptArg where
  runScriptArg = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner
  [ "Musthave typechecks"           `atDir` "typechecks"
  , "Documentation"                 `atDir` "docs"
  , "Laziness of a list"            `atDir` "laziness"
  ]
