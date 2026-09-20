import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 281 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17929) (q := 17939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17939) (q := 17957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17957) (q := 17959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17959) (q := 17971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17971) (q := 17977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17977) (q := 17981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17981) (q := 17987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17987) (q := 17989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part11_chain :
    DusartPrimeRowsChain 17929 17989 dusartPrimeRows_17159_18040_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 17929 ≤ 17929; omega
  · change 17929 ≤ 17938; omega
  · apply DusartPrimeRowsChain.cons
    · change 17939 ≤ 17939; omega
    · change 17939 ≤ 17956; omega
    · apply DusartPrimeRowsChain.cons
      · change 17957 ≤ 17957; omega
      · change 17957 ≤ 17958; omega
      · apply DusartPrimeRowsChain.cons
        · change 17959 ≤ 17959; omega
        · change 17959 ≤ 17970; omega
        · apply DusartPrimeRowsChain.cons
          · change 17971 ≤ 17971; omega
          · change 17971 ≤ 17976; omega
          · apply DusartPrimeRowsChain.cons
            · change 17977 ≤ 17977; omega
            · change 17977 ≤ 17980; omega
            · apply DusartPrimeRowsChain.cons
              · change 17981 ≤ 17981; omega
              · change 17981 ≤ 17986; omega
              · apply DusartPrimeRowsChain.cons
                · change 17987 ≤ 17987; omega
                · change 17987 ≤ 17988; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
