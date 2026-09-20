import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 202 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part10_chain :
    DusartPrimeRowsChain 17033 17117 dusartPrimeRows_16319_17158_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 17033 ≤ 17033; omega
  · change 17033 ≤ 17040; omega
  · apply DusartPrimeRowsChain.cons
    · change 17041 ≤ 17041; omega
    · change 17041 ≤ 17046; omega
    · apply DusartPrimeRowsChain.cons
      · change 17047 ≤ 17047; omega
      · change 17047 ≤ 17052; omega
      · apply DusartPrimeRowsChain.cons
        · change 17053 ≤ 17053; omega
        · change 17053 ≤ 17076; omega
        · apply DusartPrimeRowsChain.cons
          · change 17077 ≤ 17077; omega
          · change 17077 ≤ 17092; omega
          · apply DusartPrimeRowsChain.cons
            · change 17093 ≤ 17093; omega
            · change 17093 ≤ 17098; omega
            · apply DusartPrimeRowsChain.cons
              · change 17099 ≤ 17099; omega
              · change 17099 ≤ 17106; omega
              · apply DusartPrimeRowsChain.cons
                · change 17107 ≤ 17107; omega
                · change 17107 ≤ 17116; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
