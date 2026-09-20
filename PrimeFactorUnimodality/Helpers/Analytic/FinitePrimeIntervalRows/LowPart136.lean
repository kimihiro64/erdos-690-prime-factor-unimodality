import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 136 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part03_chain :
    DusartPrimeRowsChain 12241 12301 dusartPrimeRows_12097_12712_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 12241 ≤ 12241; omega
  · change 12241 ≤ 12250; omega
  · apply DusartPrimeRowsChain.cons
    · change 12251 ≤ 12251; omega
    · change 12251 ≤ 12252; omega
    · apply DusartPrimeRowsChain.cons
      · change 12253 ≤ 12253; omega
      · change 12253 ≤ 12262; omega
      · apply DusartPrimeRowsChain.cons
        · change 12263 ≤ 12263; omega
        · change 12263 ≤ 12268; omega
        · apply DusartPrimeRowsChain.cons
          · change 12269 ≤ 12269; omega
          · change 12269 ≤ 12276; omega
          · apply DusartPrimeRowsChain.cons
            · change 12277 ≤ 12277; omega
            · change 12277 ≤ 12280; omega
            · apply DusartPrimeRowsChain.cons
              · change 12281 ≤ 12281; omega
              · change 12281 ≤ 12288; omega
              · apply DusartPrimeRowsChain.cons
                · change 12289 ≤ 12289; omega
                · change 12289 ≤ 12300; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
