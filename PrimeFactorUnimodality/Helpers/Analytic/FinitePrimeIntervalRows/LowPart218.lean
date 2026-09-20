import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 218 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part15 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part15_chain :
    DusartPrimeRowsChain 23087 23159 dusartPrimeRows_22027_23158_part15 := by
  apply DusartPrimeRowsChain.cons
  · change 23087 ≤ 23087; omega
  · change 23087 ≤ 23098; omega
  · apply DusartPrimeRowsChain.cons
    · change 23099 ≤ 23099; omega
    · change 23099 ≤ 23116; omega
    · apply DusartPrimeRowsChain.cons
      · change 23117 ≤ 23117; omega
      · change 23117 ≤ 23130; omega
      · apply DusartPrimeRowsChain.cons
        · change 23131 ≤ 23131; omega
        · change 23131 ≤ 23142; omega
        · apply DusartPrimeRowsChain.cons
          · change 23143 ≤ 23143; omega
          · change 23143 ≤ 23158; omega
          · apply DusartPrimeRowsChain.empty
            norm_num
