import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart60

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 61 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part07_chain :
    DusartPrimeRowsChain 10337 10427 dusartPrimeRows_9901_10426_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426 : List DusartPrimeRow :=
  dusartPrimeRows_9901_10426_part01 ++ dusartPrimeRows_9901_10426_part02 ++ dusartPrimeRows_9901_10426_part03 ++ dusartPrimeRows_9901_10426_part04 ++ dusartPrimeRows_9901_10426_part05 ++ dusartPrimeRows_9901_10426_part06 ++ dusartPrimeRows_9901_10426_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_chain :
    DusartPrimeRowsChain 9901 10426 dusartPrimeRows_9901_10426 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_9901_10426_part06_chain (dusartPrimeRows_9901_10426_part07_chain))))))
