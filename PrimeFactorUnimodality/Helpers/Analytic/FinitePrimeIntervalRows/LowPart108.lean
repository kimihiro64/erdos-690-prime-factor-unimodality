import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 108 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part05_chain :
    DusartPrimeRowsChain 10211 10273 dusartPrimeRows_9901_10426_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 10211 ≤ 10211; omega
  · change 10211 ≤ 10222; omega
  · apply DusartPrimeRowsChain.cons
    · change 10223 ≤ 10223; omega
    · change 10223 ≤ 10242; omega
    · apply DusartPrimeRowsChain.cons
      · change 10243 ≤ 10243; omega
      · change 10243 ≤ 10246; omega
      · apply DusartPrimeRowsChain.cons
        · change 10247 ≤ 10247; omega
        · change 10247 ≤ 10252; omega
        · apply DusartPrimeRowsChain.cons
          · change 10253 ≤ 10253; omega
          · change 10253 ≤ 10258; omega
          · apply DusartPrimeRowsChain.cons
            · change 10259 ≤ 10259; omega
            · change 10259 ≤ 10266; omega
            · apply DusartPrimeRowsChain.cons
              · change 10267 ≤ 10267; omega
              · change 10267 ≤ 10270; omega
              · apply DusartPrimeRowsChain.cons
                · change 10271 ≤ 10271; omega
                · change 10271 ≤ 10272; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
