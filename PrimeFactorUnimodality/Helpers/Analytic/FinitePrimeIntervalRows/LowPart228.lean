import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 228 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21617) (q := 21647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21647) (q := 21649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21649) (q := 21661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21661) (q := 21673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21673) (q := 21683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21683) (q := 21701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21701) (q := 21713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21713) (q := 21727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part10_chain :
    DusartPrimeRowsChain 21617 21727 dusartPrimeRows_20959_22026_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 21617 ≤ 21617; omega
  · change 21617 ≤ 21646; omega
  · apply DusartPrimeRowsChain.cons
    · change 21647 ≤ 21647; omega
    · change 21647 ≤ 21648; omega
    · apply DusartPrimeRowsChain.cons
      · change 21649 ≤ 21649; omega
      · change 21649 ≤ 21660; omega
      · apply DusartPrimeRowsChain.cons
        · change 21661 ≤ 21661; omega
        · change 21661 ≤ 21672; omega
        · apply DusartPrimeRowsChain.cons
          · change 21673 ≤ 21673; omega
          · change 21673 ≤ 21682; omega
          · apply DusartPrimeRowsChain.cons
            · change 21683 ≤ 21683; omega
            · change 21683 ≤ 21700; omega
            · apply DusartPrimeRowsChain.cons
              · change 21701 ≤ 21701; omega
              · change 21701 ≤ 21712; omega
              · apply DusartPrimeRowsChain.cons
                · change 21713 ≤ 21713; omega
                · change 21713 ≤ 21726; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
