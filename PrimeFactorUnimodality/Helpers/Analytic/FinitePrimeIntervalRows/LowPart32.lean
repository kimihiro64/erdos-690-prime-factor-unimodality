import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 32 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part02_chain :
    DusartPrimeRowsChain 5233 5309 dusartPrimeRows_5167_5436_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 5233 ≤ 5233; omega
  · change 5233 ≤ 5236; omega
  · apply DusartPrimeRowsChain.cons
    · change 5237 ≤ 5237; omega
    · change 5237 ≤ 5260; omega
    · apply DusartPrimeRowsChain.cons
      · change 5261 ≤ 5261; omega
      · change 5261 ≤ 5272; omega
      · apply DusartPrimeRowsChain.cons
        · change 5273 ≤ 5273; omega
        · change 5273 ≤ 5278; omega
        · apply DusartPrimeRowsChain.cons
          · change 5279 ≤ 5279; omega
          · change 5279 ≤ 5280; omega
          · apply DusartPrimeRowsChain.cons
            · change 5281 ≤ 5281; omega
            · change 5281 ≤ 5296; omega
            · apply DusartPrimeRowsChain.cons
              · change 5297 ≤ 5297; omega
              · change 5297 ≤ 5302; omega
              · apply DusartPrimeRowsChain.cons
                · change 5303 ≤ 5303; omega
                · change 5303 ≤ 5308; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
