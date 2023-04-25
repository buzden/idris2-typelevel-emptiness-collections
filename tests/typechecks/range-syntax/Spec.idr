module Spec

import Data.CheckedEmpty.List
import Data.CheckedEmpty.List.Lazy

--- Examples ---

0 e_f_0 : Lst False Nat
e_f_0 = [1 .. 9]

0 e_f_2 : Lst False Nat
e_f_2 = [1, 5 .. 10]

0 l_f_0 : LazyLst False Nat
l_f_0 = [1 .. 9]

0 l_f_2 : LazyLst False Nat
l_f_2 = [1, 5 .. 10]

0 l_f_w : LazyLst True Nat
l_f_w = [1 ..]

0 l_h_w : LazyLst True Nat
l_h_w = [1, 5 ..]
