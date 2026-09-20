import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 96 -/

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
  apply DusartPrimeRowsChain.cons
  · change 9397 ≤ 9397; omega
  · change 9397 ≤ 9402; omega
  · apply DusartPrimeRowsChain.cons
    · change 9403 ≤ 9403; omega
    · change 9403 ≤ 9412; omega
    · apply DusartPrimeRowsChain.cons
      · change 9413 ≤ 9413; omega
      · change 9413 ≤ 9418; omega
      · apply DusartPrimeRowsChain.empty
        norm_num
