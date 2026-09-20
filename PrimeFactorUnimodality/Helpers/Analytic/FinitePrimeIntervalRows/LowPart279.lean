import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 279 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17783) (q := 17789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17789) (q := 17791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17791) (q := 17807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17807) (q := 17827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17827) (q := 17837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17837) (q := 17839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17839) (q := 17851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17851) (q := 17863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part09_chain :
    DusartPrimeRowsChain 17783 17863 dusartPrimeRows_17159_18040_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 17783 ≤ 17783; omega
  · change 17783 ≤ 17788; omega
  · apply DusartPrimeRowsChain.cons
    · change 17789 ≤ 17789; omega
    · change 17789 ≤ 17790; omega
    · apply DusartPrimeRowsChain.cons
      · change 17791 ≤ 17791; omega
      · change 17791 ≤ 17806; omega
      · apply DusartPrimeRowsChain.cons
        · change 17807 ≤ 17807; omega
        · change 17807 ≤ 17826; omega
        · apply DusartPrimeRowsChain.cons
          · change 17827 ≤ 17827; omega
          · change 17827 ≤ 17836; omega
          · apply DusartPrimeRowsChain.cons
            · change 17837 ≤ 17837; omega
            · change 17837 ≤ 17838; omega
            · apply DusartPrimeRowsChain.cons
              · change 17839 ≤ 17839; omega
              · change 17839 ≤ 17850; omega
              · apply DusartPrimeRowsChain.cons
                · change 17851 ≤ 17851; omega
                · change 17851 ≤ 17862; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
