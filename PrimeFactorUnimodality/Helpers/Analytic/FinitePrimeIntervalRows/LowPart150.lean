import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 150 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13327 dusartPrimeRows_12713_13366_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 13241 ≤ 13241; omega
  · change 13241 ≤ 13248; omega
  · apply DusartPrimeRowsChain.cons
    · change 13249 ≤ 13249; omega
    · change 13249 ≤ 13258; omega
    · apply DusartPrimeRowsChain.cons
      · change 13259 ≤ 13259; omega
      · change 13259 ≤ 13266; omega
      · apply DusartPrimeRowsChain.cons
        · change 13267 ≤ 13267; omega
        · change 13267 ≤ 13290; omega
        · apply DusartPrimeRowsChain.cons
          · change 13291 ≤ 13291; omega
          · change 13291 ≤ 13296; omega
          · apply DusartPrimeRowsChain.cons
            · change 13297 ≤ 13297; omega
            · change 13297 ≤ 13308; omega
            · apply DusartPrimeRowsChain.cons
              · change 13309 ≤ 13309; omega
              · change 13309 ≤ 13312; omega
              · apply DusartPrimeRowsChain.cons
                · change 13313 ≤ 13313; omega
                · change 13313 ≤ 13326; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
