import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part03_chain :
    DusartPrimeRowsChain 3391 3467 dusartPrimeRows_3275_3802_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 3391 ≤ 3391; omega
  · change 3391 ≤ 3406; omega
  · apply DusartPrimeRowsChain.cons
    · change 3407 ≤ 3407; omega
    · change 3407 ≤ 3412; omega
    · apply DusartPrimeRowsChain.cons
      · change 3413 ≤ 3413; omega
      · change 3413 ≤ 3432; omega
      · apply DusartPrimeRowsChain.cons
        · change 3433 ≤ 3433; omega
        · change 3433 ≤ 3448; omega
        · apply DusartPrimeRowsChain.cons
          · change 3449 ≤ 3449; omega
          · change 3449 ≤ 3456; omega
          · apply DusartPrimeRowsChain.cons
            · change 3457 ≤ 3457; omega
            · change 3457 ≤ 3460; omega
            · apply DusartPrimeRowsChain.cons
              · change 3461 ≤ 3461; omega
              · change 3461 ≤ 3462; omega
              · apply DusartPrimeRowsChain.cons
                · change 3463 ≤ 3463; omega
                · change 3463 ≤ 3466; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
