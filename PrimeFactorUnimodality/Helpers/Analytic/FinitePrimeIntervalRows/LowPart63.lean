import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 63 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part04_chain :
    DusartPrimeRowsChain 7211 7283 dusartPrimeRows_6977_7332_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 7211 ≤ 7211; omega
  · change 7211 ≤ 7212; omega
  · apply DusartPrimeRowsChain.cons
    · change 7213 ≤ 7213; omega
    · change 7213 ≤ 7218; omega
    · apply DusartPrimeRowsChain.cons
      · change 7219 ≤ 7219; omega
      · change 7219 ≤ 7228; omega
      · apply DusartPrimeRowsChain.cons
        · change 7229 ≤ 7229; omega
        · change 7229 ≤ 7236; omega
        · apply DusartPrimeRowsChain.cons
          · change 7237 ≤ 7237; omega
          · change 7237 ≤ 7242; omega
          · apply DusartPrimeRowsChain.cons
            · change 7243 ≤ 7243; omega
            · change 7243 ≤ 7246; omega
            · apply DusartPrimeRowsChain.cons
              · change 7247 ≤ 7247; omega
              · change 7247 ≤ 7252; omega
              · apply DusartPrimeRowsChain.cons
                · change 7253 ≤ 7253; omega
                · change 7253 ≤ 7282; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
