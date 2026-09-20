import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 09 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3803 dusartPrimeRows_3275_3802_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 3779 ≤ 3779; omega
  · change 3779 ≤ 3792; omega
  · apply DusartPrimeRowsChain.cons
    · change 3793 ≤ 3793; omega
    · change 3793 ≤ 3796; omega
    · apply DusartPrimeRowsChain.cons
      · change 3797 ≤ 3797; omega
      · change 3797 ≤ 3802; omega
      · apply DusartPrimeRowsChain.empty
        norm_num
