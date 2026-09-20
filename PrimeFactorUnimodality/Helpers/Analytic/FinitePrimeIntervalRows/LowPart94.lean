import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 94 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part05_chain :
    DusartPrimeRowsChain 9241 9323 dusartPrimeRows_8963_9418_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 9241 ≤ 9241; omega
  · change 9241 ≤ 9256; omega
  · apply DusartPrimeRowsChain.cons
    · change 9257 ≤ 9257; omega
    · change 9257 ≤ 9276; omega
    · apply DusartPrimeRowsChain.cons
      · change 9277 ≤ 9277; omega
      · change 9277 ≤ 9280; omega
      · apply DusartPrimeRowsChain.cons
        · change 9281 ≤ 9281; omega
        · change 9281 ≤ 9282; omega
        · apply DusartPrimeRowsChain.cons
          · change 9283 ≤ 9283; omega
          · change 9283 ≤ 9292; omega
          · apply DusartPrimeRowsChain.cons
            · change 9293 ≤ 9293; omega
            · change 9293 ≤ 9310; omega
            · apply DusartPrimeRowsChain.cons
              · change 9311 ≤ 9311; omega
              · change 9311 ≤ 9318; omega
              · apply DusartPrimeRowsChain.cons
                · change 9319 ≤ 9319; omega
                · change 9319 ≤ 9322; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
