import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 155 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part04_chain :
    DusartPrimeRowsChain 13619 13691 dusartPrimeRows_13367_14050_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 13619 ≤ 13619; omega
  · change 13619 ≤ 13626; omega
  · apply DusartPrimeRowsChain.cons
    · change 13627 ≤ 13627; omega
    · change 13627 ≤ 13632; omega
    · apply DusartPrimeRowsChain.cons
      · change 13633 ≤ 13633; omega
      · change 13633 ≤ 13648; omega
      · apply DusartPrimeRowsChain.cons
        · change 13649 ≤ 13649; omega
        · change 13649 ≤ 13668; omega
        · apply DusartPrimeRowsChain.cons
          · change 13669 ≤ 13669; omega
          · change 13669 ≤ 13678; omega
          · apply DusartPrimeRowsChain.cons
            · change 13679 ≤ 13679; omega
            · change 13679 ≤ 13680; omega
            · apply DusartPrimeRowsChain.cons
              · change 13681 ≤ 13681; omega
              · change 13681 ≤ 13686; omega
              · apply DusartPrimeRowsChain.cons
                · change 13687 ≤ 13687; omega
                · change 13687 ≤ 13690; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
