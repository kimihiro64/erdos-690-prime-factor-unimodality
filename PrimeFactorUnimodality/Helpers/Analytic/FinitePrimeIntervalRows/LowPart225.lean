import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 225 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21419) (q := 21433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21433) (q := 21467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21467) (q := 21481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21481) (q := 21487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21487) (q := 21491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21491) (q := 21493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21493) (q := 21499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21499) (q := 21503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part07_chain :
    DusartPrimeRowsChain 21419 21503 dusartPrimeRows_20959_22026_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 21419 ≤ 21419; omega
  · change 21419 ≤ 21432; omega
  · apply DusartPrimeRowsChain.cons
    · change 21433 ≤ 21433; omega
    · change 21433 ≤ 21466; omega
    · apply DusartPrimeRowsChain.cons
      · change 21467 ≤ 21467; omega
      · change 21467 ≤ 21480; omega
      · apply DusartPrimeRowsChain.cons
        · change 21481 ≤ 21481; omega
        · change 21481 ≤ 21486; omega
        · apply DusartPrimeRowsChain.cons
          · change 21487 ≤ 21487; omega
          · change 21487 ≤ 21490; omega
          · apply DusartPrimeRowsChain.cons
            · change 21491 ≤ 21491; omega
            · change 21491 ≤ 21492; omega
            · apply DusartPrimeRowsChain.cons
              · change 21493 ≤ 21493; omega
              · change 21493 ≤ 21498; omega
              · apply DusartPrimeRowsChain.cons
                · change 21499 ≤ 21499; omega
                · change 21499 ≤ 21502; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
