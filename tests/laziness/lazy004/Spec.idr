module Spec

import Data.CheckedEmpty.List.Lazy

main : IO ()
main = do
  let ll : LazyLst1 Nat := [1 ..]
  putStrLn $ show $ take 5 ll
  let ll' : LazyLst1 Nat := [1, 4 ..]
  putStrLn $ show $ take 5 ll'
