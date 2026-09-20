import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 200 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part08_chain :
    DusartPrimeRowsChain 16901 16979 dusartPrimeRows_16319_17158_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 16901 ≤ 16901; omega
  · change 16901 ≤ 16902; omega
  · apply DusartPrimeRowsChain.cons
    · change 16903 ≤ 16903; omega
    · change 16903 ≤ 16920; omega
    · apply DusartPrimeRowsChain.cons
      · change 16921 ≤ 16921; omega
      · change 16921 ≤ 16926; omega
      · apply DusartPrimeRowsChain.cons
        · change 16927 ≤ 16927; omega
        · change 16927 ≤ 16930; omega
        · apply DusartPrimeRowsChain.cons
          · change 16931 ≤ 16931; omega
          · change 16931 ≤ 16936; omega
          · apply DusartPrimeRowsChain.cons
            · change 16937 ≤ 16937; omega
            · change 16937 ≤ 16942; omega
            · apply DusartPrimeRowsChain.cons
              · change 16943 ≤ 16943; omega
              · change 16943 ≤ 16962; omega
              · apply DusartPrimeRowsChain.cons
                · change 16963 ≤ 16963; omega
                · change 16963 ≤ 16978; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
