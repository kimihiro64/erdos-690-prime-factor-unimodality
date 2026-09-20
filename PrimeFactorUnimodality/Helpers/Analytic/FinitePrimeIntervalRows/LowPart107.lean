import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 107 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part04_chain :
    DusartPrimeRowsChain 10141 10211 dusartPrimeRows_9901_10426_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 10141 ≤ 10141; omega
  · change 10141 ≤ 10150; omega
  · apply DusartPrimeRowsChain.cons
    · change 10151 ≤ 10151; omega
    · change 10151 ≤ 10158; omega
    · apply DusartPrimeRowsChain.cons
      · change 10159 ≤ 10159; omega
      · change 10159 ≤ 10162; omega
      · apply DusartPrimeRowsChain.cons
        · change 10163 ≤ 10163; omega
        · change 10163 ≤ 10168; omega
        · apply DusartPrimeRowsChain.cons
          · change 10169 ≤ 10169; omega
          · change 10169 ≤ 10176; omega
          · apply DusartPrimeRowsChain.cons
            · change 10177 ≤ 10177; omega
            · change 10177 ≤ 10180; omega
            · apply DusartPrimeRowsChain.cons
              · change 10181 ≤ 10181; omega
              · change 10181 ≤ 10192; omega
              · apply DusartPrimeRowsChain.cons
                · change 10193 ≤ 10193; omega
                · change 10193 ≤ 10210; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
