import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 101 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part05_chain :
    DusartPrimeRowsChain 9697 9769 dusartPrimeRows_9419_9900_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 9697 ≤ 9697; omega
  · change 9697 ≤ 9718; omega
  · apply DusartPrimeRowsChain.cons
    · change 9719 ≤ 9719; omega
    · change 9719 ≤ 9720; omega
    · apply DusartPrimeRowsChain.cons
      · change 9721 ≤ 9721; omega
      · change 9721 ≤ 9732; omega
      · apply DusartPrimeRowsChain.cons
        · change 9733 ≤ 9733; omega
        · change 9733 ≤ 9738; omega
        · apply DusartPrimeRowsChain.cons
          · change 9739 ≤ 9739; omega
          · change 9739 ≤ 9742; omega
          · apply DusartPrimeRowsChain.cons
            · change 9743 ≤ 9743; omega
            · change 9743 ≤ 9748; omega
            · apply DusartPrimeRowsChain.cons
              · change 9749 ≤ 9749; omega
              · change 9749 ≤ 9766; omega
              · apply DusartPrimeRowsChain.cons
                · change 9767 ≤ 9767; omega
                · change 9767 ≤ 9768; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
