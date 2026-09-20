import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 17 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part08_chain :
    DusartPrimeRowsChain 4261 4339 dusartPrimeRows_3803_4672_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 4261 ≤ 4261; omega
  · change 4261 ≤ 4270; omega
  · apply DusartPrimeRowsChain.cons
    · change 4271 ≤ 4271; omega
    · change 4271 ≤ 4272; omega
    · apply DusartPrimeRowsChain.cons
      · change 4273 ≤ 4273; omega
      · change 4273 ≤ 4282; omega
      · apply DusartPrimeRowsChain.cons
        · change 4283 ≤ 4283; omega
        · change 4283 ≤ 4288; omega
        · apply DusartPrimeRowsChain.cons
          · change 4289 ≤ 4289; omega
          · change 4289 ≤ 4296; omega
          · apply DusartPrimeRowsChain.cons
            · change 4297 ≤ 4297; omega
            · change 4297 ≤ 4326; omega
            · apply DusartPrimeRowsChain.cons
              · change 4327 ≤ 4327; omega
              · change 4327 ≤ 4336; omega
              · apply DusartPrimeRowsChain.cons
                · change 4337 ≤ 4337; omega
                · change 4337 ≤ 4338; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
