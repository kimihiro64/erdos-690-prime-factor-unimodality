import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart100

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 101 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part07_chain :
    DusartPrimeRowsChain 9397 9419 dusartPrimeRows_8963_9418_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418 : List DusartPrimeRow :=
  dusartPrimeRows_8963_9418_part01 ++ dusartPrimeRows_8963_9418_part02 ++ dusartPrimeRows_8963_9418_part03 ++ dusartPrimeRows_8963_9418_part04 ++ dusartPrimeRows_8963_9418_part05 ++ dusartPrimeRows_8963_9418_part06 ++ dusartPrimeRows_8963_9418_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_chain :
    DusartPrimeRowsChain 8963 9418 dusartPrimeRows_8963_9418 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_8963_9418_part06_chain (dusartPrimeRows_8963_9418_part07_chain))))))
