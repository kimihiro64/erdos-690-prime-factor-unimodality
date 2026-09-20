import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 19 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part10_chain :
    DusartPrimeRowsChain 4421 4483 dusartPrimeRows_3803_4672_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 4421 ≤ 4421; omega
  · change 4421 ≤ 4422; omega
  · apply DusartPrimeRowsChain.cons
    · change 4423 ≤ 4423; omega
    · change 4423 ≤ 4440; omega
    · apply DusartPrimeRowsChain.cons
      · change 4441 ≤ 4441; omega
      · change 4441 ≤ 4446; omega
      · apply DusartPrimeRowsChain.cons
        · change 4447 ≤ 4447; omega
        · change 4447 ≤ 4450; omega
        · apply DusartPrimeRowsChain.cons
          · change 4451 ≤ 4451; omega
          · change 4451 ≤ 4456; omega
          · apply DusartPrimeRowsChain.cons
            · change 4457 ≤ 4457; omega
            · change 4457 ≤ 4462; omega
            · apply DusartPrimeRowsChain.cons
              · change 4463 ≤ 4463; omega
              · change 4463 ≤ 4480; omega
              · apply DusartPrimeRowsChain.cons
                · change 4481 ≤ 4481; omega
                · change 4481 ≤ 4482; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
