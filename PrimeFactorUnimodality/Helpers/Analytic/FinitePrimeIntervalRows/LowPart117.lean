import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 117 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10939 dusartPrimeRows_10427_10938_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 10883 ≤ 10883; omega
  · change 10883 ≤ 10888; omega
  · apply DusartPrimeRowsChain.cons
    · change 10889 ≤ 10889; omega
    · change 10889 ≤ 10890; omega
    · apply DusartPrimeRowsChain.cons
      · change 10891 ≤ 10891; omega
      · change 10891 ≤ 10902; omega
      · apply DusartPrimeRowsChain.cons
        · change 10903 ≤ 10903; omega
        · change 10903 ≤ 10908; omega
        · apply DusartPrimeRowsChain.cons
          · change 10909 ≤ 10909; omega
          · change 10909 ≤ 10936; omega
          · apply DusartPrimeRowsChain.cons
            · change 10937 ≤ 10937; omega
            · change 10937 ≤ 10938; omega
            · apply DusartPrimeRowsChain.empty
              norm_num
