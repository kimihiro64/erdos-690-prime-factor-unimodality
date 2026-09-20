import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 185 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part04_chain :
    DusartPrimeRowsChain 15739 15803 dusartPrimeRows_15527_16318_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 15739 ≤ 15739; omega
  · change 15739 ≤ 15748; omega
  · apply DusartPrimeRowsChain.cons
    · change 15749 ≤ 15749; omega
    · change 15749 ≤ 15760; omega
    · apply DusartPrimeRowsChain.cons
      · change 15761 ≤ 15761; omega
      · change 15761 ≤ 15766; omega
      · apply DusartPrimeRowsChain.cons
        · change 15767 ≤ 15767; omega
        · change 15767 ≤ 15772; omega
        · apply DusartPrimeRowsChain.cons
          · change 15773 ≤ 15773; omega
          · change 15773 ≤ 15786; omega
          · apply DusartPrimeRowsChain.cons
            · change 15787 ≤ 15787; omega
            · change 15787 ≤ 15790; omega
            · apply DusartPrimeRowsChain.cons
              · change 15791 ≤ 15791; omega
              · change 15791 ≤ 15796; omega
              · apply DusartPrimeRowsChain.cons
                · change 15797 ≤ 15797; omega
                · change 15797 ≤ 15802; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
