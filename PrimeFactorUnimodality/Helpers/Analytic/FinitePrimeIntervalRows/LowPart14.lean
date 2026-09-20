import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 14 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part05_chain :
    DusartPrimeRowsChain 4073 4133 dusartPrimeRows_3803_4672_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 4073 ≤ 4073; omega
  · change 4073 ≤ 4078; omega
  · apply DusartPrimeRowsChain.cons
    · change 4079 ≤ 4079; omega
    · change 4079 ≤ 4090; omega
    · apply DusartPrimeRowsChain.cons
      · change 4091 ≤ 4091; omega
      · change 4091 ≤ 4092; omega
      · apply DusartPrimeRowsChain.cons
        · change 4093 ≤ 4093; omega
        · change 4093 ≤ 4098; omega
        · apply DusartPrimeRowsChain.cons
          · change 4099 ≤ 4099; omega
          · change 4099 ≤ 4110; omega
          · apply DusartPrimeRowsChain.cons
            · change 4111 ≤ 4111; omega
            · change 4111 ≤ 4126; omega
            · apply DusartPrimeRowsChain.cons
              · change 4127 ≤ 4127; omega
              · change 4127 ≤ 4128; omega
              · apply DusartPrimeRowsChain.cons
                · change 4129 ≤ 4129; omega
                · change 4129 ≤ 4132; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
