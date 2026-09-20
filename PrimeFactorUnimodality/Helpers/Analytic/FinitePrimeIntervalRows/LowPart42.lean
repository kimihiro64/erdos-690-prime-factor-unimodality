import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 42 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part03_chain :
    DusartPrimeRowsChain 5849 5897 dusartPrimeRows_5711_6006_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 5849 ≤ 5849; omega
  · change 5849 ≤ 5850; omega
  · apply DusartPrimeRowsChain.cons
    · change 5851 ≤ 5851; omega
    · change 5851 ≤ 5856; omega
    · apply DusartPrimeRowsChain.cons
      · change 5857 ≤ 5857; omega
      · change 5857 ≤ 5860; omega
      · apply DusartPrimeRowsChain.cons
        · change 5861 ≤ 5861; omega
        · change 5861 ≤ 5866; omega
        · apply DusartPrimeRowsChain.cons
          · change 5867 ≤ 5867; omega
          · change 5867 ≤ 5868; omega
          · apply DusartPrimeRowsChain.cons
            · change 5869 ≤ 5869; omega
            · change 5869 ≤ 5878; omega
            · apply DusartPrimeRowsChain.cons
              · change 5879 ≤ 5879; omega
              · change 5879 ≤ 5880; omega
              · apply DusartPrimeRowsChain.cons
                · change 5881 ≤ 5881; omega
                · change 5881 ≤ 5896; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
