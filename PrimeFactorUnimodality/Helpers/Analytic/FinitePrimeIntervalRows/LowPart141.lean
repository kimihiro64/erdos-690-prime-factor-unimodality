import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 141 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12647 dusartPrimeRows_12097_12712_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 12583 ≤ 12583; omega
  · change 12583 ≤ 12588; omega
  · apply DusartPrimeRowsChain.cons
    · change 12589 ≤ 12589; omega
    · change 12589 ≤ 12600; omega
    · apply DusartPrimeRowsChain.cons
      · change 12601 ≤ 12601; omega
      · change 12601 ≤ 12610; omega
      · apply DusartPrimeRowsChain.cons
        · change 12611 ≤ 12611; omega
        · change 12611 ≤ 12612; omega
        · apply DusartPrimeRowsChain.cons
          · change 12613 ≤ 12613; omega
          · change 12613 ≤ 12618; omega
          · apply DusartPrimeRowsChain.cons
            · change 12619 ≤ 12619; omega
            · change 12619 ≤ 12636; omega
            · apply DusartPrimeRowsChain.cons
              · change 12637 ≤ 12637; omega
              · change 12637 ≤ 12640; omega
              · apply DusartPrimeRowsChain.cons
                · change 12641 ≤ 12641; omega
                · change 12641 ≤ 12646; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
