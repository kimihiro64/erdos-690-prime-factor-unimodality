import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 193 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part01_chain :
    DusartPrimeRowsChain 16319 16411 dusartPrimeRows_16319_17158_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 16319 ≤ 16319; omega
  · change 16319 ≤ 16332; omega
  · apply DusartPrimeRowsChain.cons
    · change 16333 ≤ 16333; omega
    · change 16333 ≤ 16338; omega
    · apply DusartPrimeRowsChain.cons
      · change 16339 ≤ 16339; omega
      · change 16339 ≤ 16348; omega
      · apply DusartPrimeRowsChain.cons
        · change 16349 ≤ 16349; omega
        · change 16349 ≤ 16360; omega
        · apply DusartPrimeRowsChain.cons
          · change 16361 ≤ 16361; omega
          · change 16361 ≤ 16362; omega
          · apply DusartPrimeRowsChain.cons
            · change 16363 ≤ 16363; omega
            · change 16363 ≤ 16368; omega
            · apply DusartPrimeRowsChain.cons
              · change 16369 ≤ 16369; omega
              · change 16369 ≤ 16380; omega
              · apply DusartPrimeRowsChain.cons
                · change 16381 ≤ 16381; omega
                · change 16381 ≤ 16410; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
