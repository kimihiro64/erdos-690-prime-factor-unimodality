import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 229 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21727) (q := 21737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21737) (q := 21739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21739) (q := 21751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21751) (q := 21757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21757) (q := 21767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21767) (q := 21773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21773) (q := 21787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21787) (q := 21799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part11_chain :
    DusartPrimeRowsChain 21727 21799 dusartPrimeRows_20959_22026_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 21727 ≤ 21727; omega
  · change 21727 ≤ 21736; omega
  · apply DusartPrimeRowsChain.cons
    · change 21737 ≤ 21737; omega
    · change 21737 ≤ 21738; omega
    · apply DusartPrimeRowsChain.cons
      · change 21739 ≤ 21739; omega
      · change 21739 ≤ 21750; omega
      · apply DusartPrimeRowsChain.cons
        · change 21751 ≤ 21751; omega
        · change 21751 ≤ 21756; omega
        · apply DusartPrimeRowsChain.cons
          · change 21757 ≤ 21757; omega
          · change 21757 ≤ 21766; omega
          · apply DusartPrimeRowsChain.cons
            · change 21767 ≤ 21767; omega
            · change 21767 ≤ 21772; omega
            · apply DusartPrimeRowsChain.cons
              · change 21773 ≤ 21773; omega
              · change 21773 ≤ 21786; omega
              · apply DusartPrimeRowsChain.cons
                · change 21787 ≤ 21787; omega
                · change 21787 ≤ 21798; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
