import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 269 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18803) (q := 18839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18839) (q := 18859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18859) (q := 18869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18869) (q := 18899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18899) (q := 18911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18911) (q := 18913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18913) (q := 18917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18917) (q := 18919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part11_chain :
    DusartPrimeRowsChain 18803 18919 dusartPrimeRows_18041_18958_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 18803 ≤ 18803; omega
  · change 18803 ≤ 18838; omega
  · apply DusartPrimeRowsChain.cons
    · change 18839 ≤ 18839; omega
    · change 18839 ≤ 18858; omega
    · apply DusartPrimeRowsChain.cons
      · change 18859 ≤ 18859; omega
      · change 18859 ≤ 18868; omega
      · apply DusartPrimeRowsChain.cons
        · change 18869 ≤ 18869; omega
        · change 18869 ≤ 18898; omega
        · apply DusartPrimeRowsChain.cons
          · change 18899 ≤ 18899; omega
          · change 18899 ≤ 18910; omega
          · apply DusartPrimeRowsChain.cons
            · change 18911 ≤ 18911; omega
            · change 18911 ≤ 18912; omega
            · apply DusartPrimeRowsChain.cons
              · change 18913 ≤ 18913; omega
              · change 18913 ≤ 18916; omega
              · apply DusartPrimeRowsChain.cons
                · change 18917 ≤ 18917; omega
                · change 18917 ≤ 18918; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
