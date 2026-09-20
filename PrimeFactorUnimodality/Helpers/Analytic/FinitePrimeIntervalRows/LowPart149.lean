import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 149 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13241 dusartPrimeRows_12713_13366_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 13163 ≤ 13163; omega
  · change 13163 ≤ 13170; omega
  · apply DusartPrimeRowsChain.cons
    · change 13171 ≤ 13171; omega
    · change 13171 ≤ 13176; omega
    · apply DusartPrimeRowsChain.cons
      · change 13177 ≤ 13177; omega
      · change 13177 ≤ 13182; omega
      · apply DusartPrimeRowsChain.cons
        · change 13183 ≤ 13183; omega
        · change 13183 ≤ 13186; omega
        · apply DusartPrimeRowsChain.cons
          · change 13187 ≤ 13187; omega
          · change 13187 ≤ 13216; omega
          · apply DusartPrimeRowsChain.cons
            · change 13217 ≤ 13217; omega
            · change 13217 ≤ 13218; omega
            · apply DusartPrimeRowsChain.cons
              · change 13219 ≤ 13219; omega
              · change 13219 ≤ 13228; omega
              · apply DusartPrimeRowsChain.cons
                · change 13229 ≤ 13229; omega
                · change 13229 ≤ 13240; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
