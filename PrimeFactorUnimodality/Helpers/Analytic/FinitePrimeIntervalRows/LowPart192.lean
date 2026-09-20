import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 192 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part11_chain :
    DusartPrimeRowsChain 16301 16319 dusartPrimeRows_15527_16318_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 16301 ≤ 16301; omega
  · change 16301 ≤ 16318; omega
  · apply DusartPrimeRowsChain.empty
    norm_num
