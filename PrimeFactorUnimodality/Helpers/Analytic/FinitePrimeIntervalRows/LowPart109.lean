import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 109 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part06_chain :
    DusartPrimeRowsChain 10273 10337 dusartPrimeRows_9901_10426_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 10273 ≤ 10273; omega
  · change 10273 ≤ 10288; omega
  · apply DusartPrimeRowsChain.cons
    · change 10289 ≤ 10289; omega
    · change 10289 ≤ 10300; omega
    · apply DusartPrimeRowsChain.cons
      · change 10301 ≤ 10301; omega
      · change 10301 ≤ 10302; omega
      · apply DusartPrimeRowsChain.cons
        · change 10303 ≤ 10303; omega
        · change 10303 ≤ 10312; omega
        · apply DusartPrimeRowsChain.cons
          · change 10313 ≤ 10313; omega
          · change 10313 ≤ 10320; omega
          · apply DusartPrimeRowsChain.cons
            · change 10321 ≤ 10321; omega
            · change 10321 ≤ 10330; omega
            · apply DusartPrimeRowsChain.cons
              · change 10331 ≤ 10331; omega
              · change 10331 ≤ 10332; omega
              · apply DusartPrimeRowsChain.cons
                · change 10333 ≤ 10333; omega
                · change 10333 ≤ 10336; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
