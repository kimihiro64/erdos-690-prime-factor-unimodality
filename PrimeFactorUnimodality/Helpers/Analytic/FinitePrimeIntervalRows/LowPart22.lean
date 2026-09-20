import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 22 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part13_chain :
    DusartPrimeRowsChain 4637 4673 dusartPrimeRows_3803_4672_part13 := by
  apply DusartPrimeRowsChain.cons
  · change 4637 ≤ 4637; omega
  · change 4637 ≤ 4638; omega
  · apply DusartPrimeRowsChain.cons
    · change 4639 ≤ 4639; omega
    · change 4639 ≤ 4642; omega
    · apply DusartPrimeRowsChain.cons
      · change 4643 ≤ 4643; omega
      · change 4643 ≤ 4648; omega
      · apply DusartPrimeRowsChain.cons
        · change 4649 ≤ 4649; omega
        · change 4649 ≤ 4650; omega
        · apply DusartPrimeRowsChain.cons
          · change 4651 ≤ 4651; omega
          · change 4651 ≤ 4656; omega
          · apply DusartPrimeRowsChain.cons
            · change 4657 ≤ 4657; omega
            · change 4657 ≤ 4662; omega
            · apply DusartPrimeRowsChain.cons
              · change 4663 ≤ 4663; omega
              · change 4663 ≤ 4672; omega
              · apply DusartPrimeRowsChain.empty
                norm_num
