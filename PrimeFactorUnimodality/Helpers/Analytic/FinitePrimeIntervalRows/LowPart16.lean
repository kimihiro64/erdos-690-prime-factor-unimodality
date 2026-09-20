import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 16 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part07_chain :
    DusartPrimeRowsChain 4217 4261 dusartPrimeRows_3803_4672_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 4217 ≤ 4217; omega
  · change 4217 ≤ 4218; omega
  · apply DusartPrimeRowsChain.cons
    · change 4219 ≤ 4219; omega
    · change 4219 ≤ 4228; omega
    · apply DusartPrimeRowsChain.cons
      · change 4229 ≤ 4229; omega
      · change 4229 ≤ 4230; omega
      · apply DusartPrimeRowsChain.cons
        · change 4231 ≤ 4231; omega
        · change 4231 ≤ 4240; omega
        · apply DusartPrimeRowsChain.cons
          · change 4241 ≤ 4241; omega
          · change 4241 ≤ 4242; omega
          · apply DusartPrimeRowsChain.cons
            · change 4243 ≤ 4243; omega
            · change 4243 ≤ 4252; omega
            · apply DusartPrimeRowsChain.cons
              · change 4253 ≤ 4253; omega
              · change 4253 ≤ 4258; omega
              · apply DusartPrimeRowsChain.cons
                · change 4259 ≤ 4259; omega
                · change 4259 ≤ 4260; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
