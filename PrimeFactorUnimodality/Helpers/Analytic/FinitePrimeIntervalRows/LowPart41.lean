import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 41 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part02_chain :
    DusartPrimeRowsChain 5791 5849 dusartPrimeRows_5711_6006_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 5791 ≤ 5791; omega
  · change 5791 ≤ 5800; omega
  · apply DusartPrimeRowsChain.cons
    · change 5801 ≤ 5801; omega
    · change 5801 ≤ 5806; omega
    · apply DusartPrimeRowsChain.cons
      · change 5807 ≤ 5807; omega
      · change 5807 ≤ 5812; omega
      · apply DusartPrimeRowsChain.cons
        · change 5813 ≤ 5813; omega
        · change 5813 ≤ 5820; omega
        · apply DusartPrimeRowsChain.cons
          · change 5821 ≤ 5821; omega
          · change 5821 ≤ 5826; omega
          · apply DusartPrimeRowsChain.cons
            · change 5827 ≤ 5827; omega
            · change 5827 ≤ 5838; omega
            · apply DusartPrimeRowsChain.cons
              · change 5839 ≤ 5839; omega
              · change 5839 ≤ 5842; omega
              · apply DusartPrimeRowsChain.cons
                · change 5843 ≤ 5843; omega
                · change 5843 ≤ 5848; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
