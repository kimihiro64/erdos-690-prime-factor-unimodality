import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 194 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part02_chain :
    DusartPrimeRowsChain 16411 16477 dusartPrimeRows_16319_17158_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 16411 ≤ 16411; omega
  · change 16411 ≤ 16416; omega
  · apply DusartPrimeRowsChain.cons
    · change 16417 ≤ 16417; omega
    · change 16417 ≤ 16420; omega
    · apply DusartPrimeRowsChain.cons
      · change 16421 ≤ 16421; omega
      · change 16421 ≤ 16426; omega
      · apply DusartPrimeRowsChain.cons
        · change 16427 ≤ 16427; omega
        · change 16427 ≤ 16432; omega
        · apply DusartPrimeRowsChain.cons
          · change 16433 ≤ 16433; omega
          · change 16433 ≤ 16446; omega
          · apply DusartPrimeRowsChain.cons
            · change 16447 ≤ 16447; omega
            · change 16447 ≤ 16450; omega
            · apply DusartPrimeRowsChain.cons
              · change 16451 ≤ 16451; omega
              · change 16451 ≤ 16452; omega
              · apply DusartPrimeRowsChain.cons
                · change 16453 ≤ 16453; omega
                · change 16453 ≤ 16476; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
