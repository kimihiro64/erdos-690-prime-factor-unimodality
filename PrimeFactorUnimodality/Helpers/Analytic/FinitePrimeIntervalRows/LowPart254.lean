import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 254 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19571) (q := 19577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19577) (q := 19583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19583) (q := 19597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19597) (q := 19603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19603) (q := 19609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19609) (q := 19661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19661) (q := 19681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19681) (q := 19687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part09_chain :
    DusartPrimeRowsChain 19571 19687 dusartPrimeRows_18959_19936_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 19571 ≤ 19571; omega
  · change 19571 ≤ 19576; omega
  · apply DusartPrimeRowsChain.cons
    · change 19577 ≤ 19577; omega
    · change 19577 ≤ 19582; omega
    · apply DusartPrimeRowsChain.cons
      · change 19583 ≤ 19583; omega
      · change 19583 ≤ 19596; omega
      · apply DusartPrimeRowsChain.cons
        · change 19597 ≤ 19597; omega
        · change 19597 ≤ 19602; omega
        · apply DusartPrimeRowsChain.cons
          · change 19603 ≤ 19603; omega
          · change 19603 ≤ 19608; omega
          · apply DusartPrimeRowsChain.cons
            · change 19609 ≤ 19609; omega
            · change 19609 ≤ 19660; omega
            · apply DusartPrimeRowsChain.cons
              · change 19661 ≤ 19661; omega
              · change 19661 ≤ 19680; omega
              · apply DusartPrimeRowsChain.cons
                · change 19681 ≤ 19681; omega
                · change 19681 ≤ 19686; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
