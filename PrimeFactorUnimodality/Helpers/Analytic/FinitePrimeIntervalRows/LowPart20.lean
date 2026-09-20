import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart19

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 20 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426 : List DusartPrimeRow :=
  dusartPrimeRows_9901_10426_part01 ++ dusartPrimeRows_9901_10426_part02 ++ dusartPrimeRows_9901_10426_part03 ++ dusartPrimeRows_9901_10426_part04 ++ dusartPrimeRows_9901_10426_part05 ++ dusartPrimeRows_9901_10426_part06 ++ dusartPrimeRows_9901_10426_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_chain :
    DusartPrimeRowsChain 9901 10426 dusartPrimeRows_9901_10426 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part06_chain (dusartPrimeRows_9901_10426_part07_chain))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_10426 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9900 ++ dusartPrimeRows_9901_10426

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10426_chain :
    DusartPrimeRowsChain 3275 10426 dusartPrimeRows_3275_10426 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9900_chain dusartPrimeRows_9901_10426_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part01_chain :
    DusartPrimeRowsChain 10427 10487 dusartPrimeRows_10427_10938_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part02_chain :
    DusartPrimeRowsChain 10487 10589 dusartPrimeRows_10427_10938_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part03_chain :
    DusartPrimeRowsChain 10589 10651 dusartPrimeRows_10427_10938_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part04_chain :
    DusartPrimeRowsChain 10651 10723 dusartPrimeRows_10427_10938_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part05_chain :
    DusartPrimeRowsChain 10723 10799 dusartPrimeRows_10427_10938_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
