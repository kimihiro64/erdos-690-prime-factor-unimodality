import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 132 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part07_chain :
    DusartPrimeRowsChain 11971 12049 dusartPrimeRows_11503_12096_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 11971 ≤ 11971; omega
  · change 11971 ≤ 11980; omega
  · apply DusartPrimeRowsChain.cons
    · change 11981 ≤ 11981; omega
    · change 11981 ≤ 11986; omega
    · apply DusartPrimeRowsChain.cons
      · change 11987 ≤ 11987; omega
      · change 11987 ≤ 12006; omega
      · apply DusartPrimeRowsChain.cons
        · change 12007 ≤ 12007; omega
        · change 12007 ≤ 12010; omega
        · apply DusartPrimeRowsChain.cons
          · change 12011 ≤ 12011; omega
          · change 12011 ≤ 12036; omega
          · apply DusartPrimeRowsChain.cons
            · change 12037 ≤ 12037; omega
            · change 12037 ≤ 12040; omega
            · apply DusartPrimeRowsChain.cons
              · change 12041 ≤ 12041; omega
              · change 12041 ≤ 12042; omega
              · apply DusartPrimeRowsChain.cons
                · change 12043 ≤ 12043; omega
                · change 12043 ≤ 12048; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
