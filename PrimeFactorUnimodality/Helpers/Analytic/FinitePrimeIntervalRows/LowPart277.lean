import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 277 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17599) (q := 17609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17609) (q := 17623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17623) (q := 17627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17627) (q := 17657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17657) (q := 17659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17659) (q := 17669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17669) (q := 17681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17681) (q := 17683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part07_chain :
    DusartPrimeRowsChain 17599 17683 dusartPrimeRows_17159_18040_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 17599 ≤ 17599; omega
  · change 17599 ≤ 17608; omega
  · apply DusartPrimeRowsChain.cons
    · change 17609 ≤ 17609; omega
    · change 17609 ≤ 17622; omega
    · apply DusartPrimeRowsChain.cons
      · change 17623 ≤ 17623; omega
      · change 17623 ≤ 17626; omega
      · apply DusartPrimeRowsChain.cons
        · change 17627 ≤ 17627; omega
        · change 17627 ≤ 17656; omega
        · apply DusartPrimeRowsChain.cons
          · change 17657 ≤ 17657; omega
          · change 17657 ≤ 17658; omega
          · apply DusartPrimeRowsChain.cons
            · change 17659 ≤ 17659; omega
            · change 17659 ≤ 17668; omega
            · apply DusartPrimeRowsChain.cons
              · change 17669 ≤ 17669; omega
              · change 17669 ≤ 17680; omega
              · apply DusartPrimeRowsChain.cons
                · change 17681 ≤ 17681; omega
                · change 17681 ≤ 17682; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
