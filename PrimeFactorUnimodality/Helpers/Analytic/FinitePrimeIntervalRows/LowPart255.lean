import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 255 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19687) (q := 19697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19697) (q := 19699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19699) (q := 19709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19709) (q := 19717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19717) (q := 19727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19727) (q := 19739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19739) (q := 19751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19751) (q := 19753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part10_chain :
    DusartPrimeRowsChain 19687 19753 dusartPrimeRows_18959_19936_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 19687 ≤ 19687; omega
  · change 19687 ≤ 19696; omega
  · apply DusartPrimeRowsChain.cons
    · change 19697 ≤ 19697; omega
    · change 19697 ≤ 19698; omega
    · apply DusartPrimeRowsChain.cons
      · change 19699 ≤ 19699; omega
      · change 19699 ≤ 19708; omega
      · apply DusartPrimeRowsChain.cons
        · change 19709 ≤ 19709; omega
        · change 19709 ≤ 19716; omega
        · apply DusartPrimeRowsChain.cons
          · change 19717 ≤ 19717; omega
          · change 19717 ≤ 19726; omega
          · apply DusartPrimeRowsChain.cons
            · change 19727 ≤ 19727; omega
            · change 19727 ≤ 19738; omega
            · apply DusartPrimeRowsChain.cons
              · change 19739 ≤ 19739; omega
              · change 19739 ≤ 19750; omega
              · apply DusartPrimeRowsChain.cons
                · change 19751 ≤ 19751; omega
                · change 19751 ≤ 19752; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
