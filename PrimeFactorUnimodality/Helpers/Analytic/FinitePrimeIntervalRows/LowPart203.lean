import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 203 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part11_chain :
    DusartPrimeRowsChain 17117 17159 dusartPrimeRows_16319_17158_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 17117 ≤ 17117; omega
  · change 17117 ≤ 17122; omega
  · apply DusartPrimeRowsChain.cons
    · change 17123 ≤ 17123; omega
    · change 17123 ≤ 17136; omega
    · apply DusartPrimeRowsChain.cons
      · change 17137 ≤ 17137; omega
      · change 17137 ≤ 17158; omega
      · apply DusartPrimeRowsChain.empty
        norm_num
