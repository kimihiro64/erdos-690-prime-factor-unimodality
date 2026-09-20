import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part03_chain :
    DusartPrimeRowsChain 3929 4007 dusartPrimeRows_3803_4672_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 3929 ≤ 3929; omega
  · change 3929 ≤ 3930; omega
  · apply DusartPrimeRowsChain.cons
    · change 3931 ≤ 3931; omega
    · change 3931 ≤ 3942; omega
    · apply DusartPrimeRowsChain.cons
      · change 3943 ≤ 3943; omega
      · change 3943 ≤ 3946; omega
      · apply DusartPrimeRowsChain.cons
        · change 3947 ≤ 3947; omega
        · change 3947 ≤ 3966; omega
        · apply DusartPrimeRowsChain.cons
          · change 3967 ≤ 3967; omega
          · change 3967 ≤ 3988; omega
          · apply DusartPrimeRowsChain.cons
            · change 3989 ≤ 3989; omega
            · change 3989 ≤ 4000; omega
            · apply DusartPrimeRowsChain.cons
              · change 4001 ≤ 4001; omega
              · change 4001 ≤ 4002; omega
              · apply DusartPrimeRowsChain.cons
                · change 4003 ≤ 4003; omega
                · change 4003 ≤ 4006; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
