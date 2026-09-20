import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 142 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12713 dusartPrimeRows_12097_12712_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 12647 ≤ 12647; omega
  · change 12647 ≤ 12652; omega
  · apply DusartPrimeRowsChain.cons
    · change 12653 ≤ 12653; omega
    · change 12653 ≤ 12658; omega
    · apply DusartPrimeRowsChain.cons
      · change 12659 ≤ 12659; omega
      · change 12659 ≤ 12670; omega
      · apply DusartPrimeRowsChain.cons
        · change 12671 ≤ 12671; omega
        · change 12671 ≤ 12688; omega
        · apply DusartPrimeRowsChain.cons
          · change 12689 ≤ 12689; omega
          · change 12689 ≤ 12696; omega
          · apply DusartPrimeRowsChain.cons
            · change 12697 ≤ 12697; omega
            · change 12697 ≤ 12702; omega
            · apply DusartPrimeRowsChain.cons
              · change 12703 ≤ 12703; omega
              · change 12703 ≤ 12712; omega
              · apply DusartPrimeRowsChain.empty
                norm_num
