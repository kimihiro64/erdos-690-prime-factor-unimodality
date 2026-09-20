import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 140 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12583 dusartPrimeRows_12097_12712_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 12517 ≤ 12517; omega
  · change 12517 ≤ 12526; omega
  · apply DusartPrimeRowsChain.cons
    · change 12527 ≤ 12527; omega
    · change 12527 ≤ 12538; omega
    · apply DusartPrimeRowsChain.cons
      · change 12539 ≤ 12539; omega
      · change 12539 ≤ 12540; omega
      · apply DusartPrimeRowsChain.cons
        · change 12541 ≤ 12541; omega
        · change 12541 ≤ 12546; omega
        · apply DusartPrimeRowsChain.cons
          · change 12547 ≤ 12547; omega
          · change 12547 ≤ 12552; omega
          · apply DusartPrimeRowsChain.cons
            · change 12553 ≤ 12553; omega
            · change 12553 ≤ 12568; omega
            · apply DusartPrimeRowsChain.cons
              · change 12569 ≤ 12569; omega
              · change 12569 ≤ 12576; omega
              · apply DusartPrimeRowsChain.cons
                · change 12577 ≤ 12577; omega
                · change 12577 ≤ 12582; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
