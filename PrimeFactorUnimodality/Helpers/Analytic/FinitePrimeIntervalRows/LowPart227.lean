import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 227 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21569) (q := 21577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21577) (q := 21587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21587) (q := 21589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21589) (q := 21599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21599) (q := 21601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21601) (q := 21611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21611) (q := 21613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21613) (q := 21617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part09_chain :
    DusartPrimeRowsChain 21569 21617 dusartPrimeRows_20959_22026_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 21569 ≤ 21569; omega
  · change 21569 ≤ 21576; omega
  · apply DusartPrimeRowsChain.cons
    · change 21577 ≤ 21577; omega
    · change 21577 ≤ 21586; omega
    · apply DusartPrimeRowsChain.cons
      · change 21587 ≤ 21587; omega
      · change 21587 ≤ 21588; omega
      · apply DusartPrimeRowsChain.cons
        · change 21589 ≤ 21589; omega
        · change 21589 ≤ 21598; omega
        · apply DusartPrimeRowsChain.cons
          · change 21599 ≤ 21599; omega
          · change 21599 ≤ 21600; omega
          · apply DusartPrimeRowsChain.cons
            · change 21601 ≤ 21601; omega
            · change 21601 ≤ 21610; omega
            · apply DusartPrimeRowsChain.cons
              · change 21611 ≤ 21611; omega
              · change 21611 ≤ 21612; omega
              · apply DusartPrimeRowsChain.cons
                · change 21613 ≤ 21613; omega
                · change 21613 ≤ 21616; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
