import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 237 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20219) (q := 20231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20231) (q := 20233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20233) (q := 20249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20249) (q := 20261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20261) (q := 20269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20269) (q := 20287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20287) (q := 20297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20297) (q := 20323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part05_chain :
    DusartPrimeRowsChain 20219 20323 dusartPrimeRows_19937_20958_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 20219 ≤ 20219; omega
  · change 20219 ≤ 20230; omega
  · apply DusartPrimeRowsChain.cons
    · change 20231 ≤ 20231; omega
    · change 20231 ≤ 20232; omega
    · apply DusartPrimeRowsChain.cons
      · change 20233 ≤ 20233; omega
      · change 20233 ≤ 20248; omega
      · apply DusartPrimeRowsChain.cons
        · change 20249 ≤ 20249; omega
        · change 20249 ≤ 20260; omega
        · apply DusartPrimeRowsChain.cons
          · change 20261 ≤ 20261; omega
          · change 20261 ≤ 20268; omega
          · apply DusartPrimeRowsChain.cons
            · change 20269 ≤ 20269; omega
            · change 20269 ≤ 20286; omega
            · apply DusartPrimeRowsChain.cons
              · change 20287 ≤ 20287; omega
              · change 20287 ≤ 20296; omega
              · apply DusartPrimeRowsChain.cons
                · change 20297 ≤ 20297; omega
                · change 20297 ≤ 20322; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
