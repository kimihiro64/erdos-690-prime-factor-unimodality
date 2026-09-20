import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 113 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part03_chain :
    DusartPrimeRowsChain 10589 10651 dusartPrimeRows_10427_10938_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 10589 ≤ 10589; omega
  · change 10589 ≤ 10596; omega
  · apply DusartPrimeRowsChain.cons
    · change 10597 ≤ 10597; omega
    · change 10597 ≤ 10600; omega
    · apply DusartPrimeRowsChain.cons
      · change 10601 ≤ 10601; omega
      · change 10601 ≤ 10606; omega
      · apply DusartPrimeRowsChain.cons
        · change 10607 ≤ 10607; omega
        · change 10607 ≤ 10612; omega
        · apply DusartPrimeRowsChain.cons
          · change 10613 ≤ 10613; omega
          · change 10613 ≤ 10626; omega
          · apply DusartPrimeRowsChain.cons
            · change 10627 ≤ 10627; omega
            · change 10627 ≤ 10630; omega
            · apply DusartPrimeRowsChain.cons
              · change 10631 ≤ 10631; omega
              · change 10631 ≤ 10638; omega
              · apply DusartPrimeRowsChain.cons
                · change 10639 ≤ 10639; omega
                · change 10639 ≤ 10650; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
