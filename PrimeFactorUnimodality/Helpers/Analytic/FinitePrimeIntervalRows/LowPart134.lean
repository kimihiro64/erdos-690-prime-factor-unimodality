import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 134 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part01_chain :
    DusartPrimeRowsChain 12097 12157 dusartPrimeRows_12097_12712_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 12097 ≤ 12097; omega
  · change 12097 ≤ 12100; omega
  · apply DusartPrimeRowsChain.cons
    · change 12101 ≤ 12101; omega
    · change 12101 ≤ 12106; omega
    · apply DusartPrimeRowsChain.cons
      · change 12107 ≤ 12107; omega
      · change 12107 ≤ 12108; omega
      · apply DusartPrimeRowsChain.cons
        · change 12109 ≤ 12109; omega
        · change 12109 ≤ 12112; omega
        · apply DusartPrimeRowsChain.cons
          · change 12113 ≤ 12113; omega
          · change 12113 ≤ 12118; omega
          · apply DusartPrimeRowsChain.cons
            · change 12119 ≤ 12119; omega
            · change 12119 ≤ 12142; omega
            · apply DusartPrimeRowsChain.cons
              · change 12143 ≤ 12143; omega
              · change 12143 ≤ 12148; omega
              · apply DusartPrimeRowsChain.cons
                · change 12149 ≤ 12149; omega
                · change 12149 ≤ 12156; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
