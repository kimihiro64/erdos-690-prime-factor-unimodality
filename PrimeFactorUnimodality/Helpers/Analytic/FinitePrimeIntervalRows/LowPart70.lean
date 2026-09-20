import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 70 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7717 dusartPrimeRows_7333_7716_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 7687 ≤ 7687; omega
  · change 7687 ≤ 7690; omega
  · apply DusartPrimeRowsChain.cons
    · change 7691 ≤ 7691; omega
    · change 7691 ≤ 7698; omega
    · apply DusartPrimeRowsChain.cons
      · change 7699 ≤ 7699; omega
      · change 7699 ≤ 7702; omega
      · apply DusartPrimeRowsChain.cons
        · change 7703 ≤ 7703; omega
        · change 7703 ≤ 7716; omega
        · apply DusartPrimeRowsChain.empty
          norm_num
