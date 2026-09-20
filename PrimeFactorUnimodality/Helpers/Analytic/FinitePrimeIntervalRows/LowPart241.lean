import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 241 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20543) (q := 20549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20549) (q := 20551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20551) (q := 20563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20563) (q := 20593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20593) (q := 20599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20599) (q := 20611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20611) (q := 20627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20627) (q := 20639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part09_chain :
    DusartPrimeRowsChain 20543 20639 dusartPrimeRows_19937_20958_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 20543 ≤ 20543; omega
  · change 20543 ≤ 20548; omega
  · apply DusartPrimeRowsChain.cons
    · change 20549 ≤ 20549; omega
    · change 20549 ≤ 20550; omega
    · apply DusartPrimeRowsChain.cons
      · change 20551 ≤ 20551; omega
      · change 20551 ≤ 20562; omega
      · apply DusartPrimeRowsChain.cons
        · change 20563 ≤ 20563; omega
        · change 20563 ≤ 20592; omega
        · apply DusartPrimeRowsChain.cons
          · change 20593 ≤ 20593; omega
          · change 20593 ≤ 20598; omega
          · apply DusartPrimeRowsChain.cons
            · change 20599 ≤ 20599; omega
            · change 20599 ≤ 20610; omega
            · apply DusartPrimeRowsChain.cons
              · change 20611 ≤ 20611; omega
              · change 20611 ≤ 20626; omega
              · apply DusartPrimeRowsChain.cons
                · change 20627 ≤ 20627; omega
                · change 20627 ≤ 20638; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
