import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 25 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part03_chain :
    DusartPrimeRowsChain 4813 4909 dusartPrimeRows_4673_4918_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 4813 ≤ 4813; omega
  · change 4813 ≤ 4816; omega
  · apply DusartPrimeRowsChain.cons
    · change 4817 ≤ 4817; omega
    · change 4817 ≤ 4830; omega
    · apply DusartPrimeRowsChain.cons
      · change 4831 ≤ 4831; omega
      · change 4831 ≤ 4860; omega
      · apply DusartPrimeRowsChain.cons
        · change 4861 ≤ 4861; omega
        · change 4861 ≤ 4870; omega
        · apply DusartPrimeRowsChain.cons
          · change 4871 ≤ 4871; omega
          · change 4871 ≤ 4876; omega
          · apply DusartPrimeRowsChain.cons
            · change 4877 ≤ 4877; omega
            · change 4877 ≤ 4888; omega
            · apply DusartPrimeRowsChain.cons
              · change 4889 ≤ 4889; omega
              · change 4889 ≤ 4902; omega
              · apply DusartPrimeRowsChain.cons
                · change 4903 ≤ 4903; omega
                · change 4903 ≤ 4908; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
