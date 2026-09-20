import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 275 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17467) (q := 17471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17471) (q := 17477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17477) (q := 17483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17483) (q := 17489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17489) (q := 17491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17491) (q := 17497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17497) (q := 17509) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17509) (q := 17519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part05_chain :
    DusartPrimeRowsChain 17467 17519 dusartPrimeRows_17159_18040_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 17467 ≤ 17467; omega
  · change 17467 ≤ 17470; omega
  · apply DusartPrimeRowsChain.cons
    · change 17471 ≤ 17471; omega
    · change 17471 ≤ 17476; omega
    · apply DusartPrimeRowsChain.cons
      · change 17477 ≤ 17477; omega
      · change 17477 ≤ 17482; omega
      · apply DusartPrimeRowsChain.cons
        · change 17483 ≤ 17483; omega
        · change 17483 ≤ 17488; omega
        · apply DusartPrimeRowsChain.cons
          · change 17489 ≤ 17489; omega
          · change 17489 ≤ 17490; omega
          · apply DusartPrimeRowsChain.cons
            · change 17491 ≤ 17491; omega
            · change 17491 ≤ 17496; omega
            · apply DusartPrimeRowsChain.cons
              · change 17497 ≤ 17497; omega
              · change 17497 ≤ 17508; omega
              · apply DusartPrimeRowsChain.cons
                · change 17509 ≤ 17509; omega
                · change 17509 ≤ 17518; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
