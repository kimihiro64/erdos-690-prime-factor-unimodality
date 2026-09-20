import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 82 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part06_chain :
    DusartPrimeRowsChain 8501 8521 dusartPrimeRows_8111_8520_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 8501 ≤ 8501; omega
  · change 8501 ≤ 8512; omega
  · apply DusartPrimeRowsChain.cons
    · change 8513 ≤ 8513; omega
    · change 8513 ≤ 8520; omega
    · apply DusartPrimeRowsChain.empty
      norm_num
