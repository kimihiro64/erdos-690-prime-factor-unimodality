import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 93 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part04_chain :
    DusartPrimeRowsChain 9181 9241 dusartPrimeRows_8963_9418_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 9181 ≤ 9181; omega
  · change 9181 ≤ 9186; omega
  · apply DusartPrimeRowsChain.cons
    · change 9187 ≤ 9187; omega
    · change 9187 ≤ 9198; omega
    · apply DusartPrimeRowsChain.cons
      · change 9199 ≤ 9199; omega
      · change 9199 ≤ 9202; omega
      · apply DusartPrimeRowsChain.cons
        · change 9203 ≤ 9203; omega
        · change 9203 ≤ 9208; omega
        · apply DusartPrimeRowsChain.cons
          · change 9209 ≤ 9209; omega
          · change 9209 ≤ 9220; omega
          · apply DusartPrimeRowsChain.cons
            · change 9221 ≤ 9221; omega
            · change 9221 ≤ 9226; omega
            · apply DusartPrimeRowsChain.cons
              · change 9227 ≤ 9227; omega
              · change 9227 ≤ 9238; omega
              · apply DusartPrimeRowsChain.cons
                · change 9239 ≤ 9239; omega
                · change 9239 ≤ 9240; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
