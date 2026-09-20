import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 24 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part02_chain :
    DusartPrimeRowsChain 4751 4813 dusartPrimeRows_4673_4918_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 4751 ≤ 4751; omega
  · change 4751 ≤ 4758; omega
  · apply DusartPrimeRowsChain.cons
    · change 4759 ≤ 4759; omega
    · change 4759 ≤ 4782; omega
    · apply DusartPrimeRowsChain.cons
      · change 4783 ≤ 4783; omega
      · change 4783 ≤ 4786; omega
      · apply DusartPrimeRowsChain.cons
        · change 4787 ≤ 4787; omega
        · change 4787 ≤ 4788; omega
        · apply DusartPrimeRowsChain.cons
          · change 4789 ≤ 4789; omega
          · change 4789 ≤ 4792; omega
          · apply DusartPrimeRowsChain.cons
            · change 4793 ≤ 4793; omega
            · change 4793 ≤ 4798; omega
            · apply DusartPrimeRowsChain.cons
              · change 4799 ≤ 4799; omega
              · change 4799 ≤ 4800; omega
              · apply DusartPrimeRowsChain.cons
                · change 4801 ≤ 4801; omega
                · change 4801 ≤ 4812; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
