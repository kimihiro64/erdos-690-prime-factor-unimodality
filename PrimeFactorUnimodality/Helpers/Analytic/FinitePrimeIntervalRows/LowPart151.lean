import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 151 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13367 dusartPrimeRows_12713_13366_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 13327 ≤ 13327; omega
  · change 13327 ≤ 13330; omega
  · apply DusartPrimeRowsChain.cons
    · change 13331 ≤ 13331; omega
    · change 13331 ≤ 13336; omega
    · apply DusartPrimeRowsChain.cons
      · change 13337 ≤ 13337; omega
      · change 13337 ≤ 13338; omega
      · apply DusartPrimeRowsChain.cons
        · change 13339 ≤ 13339; omega
        · change 13339 ≤ 13366; omega
        · apply DusartPrimeRowsChain.empty
          norm_num
