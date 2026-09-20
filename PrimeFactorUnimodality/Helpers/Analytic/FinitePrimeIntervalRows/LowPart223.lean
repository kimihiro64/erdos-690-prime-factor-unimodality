import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 223 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21269) (q := 21277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21277) (q := 21283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21283) (q := 21313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21313) (q := 21317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21317) (q := 21319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21319) (q := 21323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21323) (q := 21341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21341) (q := 21347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part05_chain :
    DusartPrimeRowsChain 21269 21347 dusartPrimeRows_20959_22026_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 21269 ≤ 21269; omega
  · change 21269 ≤ 21276; omega
  · apply DusartPrimeRowsChain.cons
    · change 21277 ≤ 21277; omega
    · change 21277 ≤ 21282; omega
    · apply DusartPrimeRowsChain.cons
      · change 21283 ≤ 21283; omega
      · change 21283 ≤ 21312; omega
      · apply DusartPrimeRowsChain.cons
        · change 21313 ≤ 21313; omega
        · change 21313 ≤ 21316; omega
        · apply DusartPrimeRowsChain.cons
          · change 21317 ≤ 21317; omega
          · change 21317 ≤ 21318; omega
          · apply DusartPrimeRowsChain.cons
            · change 21319 ≤ 21319; omega
            · change 21319 ≤ 21322; omega
            · apply DusartPrimeRowsChain.cons
              · change 21323 ≤ 21323; omega
              · change 21323 ≤ 21340; omega
              · apply DusartPrimeRowsChain.cons
                · change 21341 ≤ 21341; omega
                · change 21341 ≤ 21346; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
