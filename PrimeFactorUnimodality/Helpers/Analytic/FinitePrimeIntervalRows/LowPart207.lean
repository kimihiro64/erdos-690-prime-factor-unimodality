import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 207 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part04_chain :
    DusartPrimeRowsChain 22247 22303 dusartPrimeRows_22027_23158_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 22247 ≤ 22247; omega
  · change 22247 ≤ 22258; omega
  · apply DusartPrimeRowsChain.cons
    · change 22259 ≤ 22259; omega
    · change 22259 ≤ 22270; omega
    · apply DusartPrimeRowsChain.cons
      · change 22271 ≤ 22271; omega
      · change 22271 ≤ 22272; omega
      · apply DusartPrimeRowsChain.cons
        · change 22273 ≤ 22273; omega
        · change 22273 ≤ 22276; omega
        · apply DusartPrimeRowsChain.cons
          · change 22277 ≤ 22277; omega
          · change 22277 ≤ 22278; omega
          · apply DusartPrimeRowsChain.cons
            · change 22279 ≤ 22279; omega
            · change 22279 ≤ 22282; omega
            · apply DusartPrimeRowsChain.cons
              · change 22283 ≤ 22283; omega
              · change 22283 ≤ 22290; omega
              · apply DusartPrimeRowsChain.cons
                · change 22291 ≤ 22291; omega
                · change 22291 ≤ 22302; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
