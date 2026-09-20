import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 195 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part03_chain :
    DusartPrimeRowsChain 16477 16561 dusartPrimeRows_16319_17158_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 16477 ≤ 16477; omega
  · change 16477 ≤ 16480; omega
  · apply DusartPrimeRowsChain.cons
    · change 16481 ≤ 16481; omega
    · change 16481 ≤ 16486; omega
    · apply DusartPrimeRowsChain.cons
      · change 16487 ≤ 16487; omega
      · change 16487 ≤ 16492; omega
      · apply DusartPrimeRowsChain.cons
        · change 16493 ≤ 16493; omega
        · change 16493 ≤ 16518; omega
        · apply DusartPrimeRowsChain.cons
          · change 16519 ≤ 16519; omega
          · change 16519 ≤ 16528; omega
          · apply DusartPrimeRowsChain.cons
            · change 16529 ≤ 16529; omega
            · change 16529 ≤ 16546; omega
            · apply DusartPrimeRowsChain.cons
              · change 16547 ≤ 16547; omega
              · change 16547 ≤ 16552; omega
              · apply DusartPrimeRowsChain.cons
                · change 16553 ≤ 16553; omega
                · change 16553 ≤ 16560; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
