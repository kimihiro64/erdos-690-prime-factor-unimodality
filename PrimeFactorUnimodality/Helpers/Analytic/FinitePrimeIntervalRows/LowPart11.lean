import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 11 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part02_chain :
    DusartPrimeRowsChain 3877 3929 dusartPrimeRows_3803_4672_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 3877 ≤ 3877; omega
  · change 3877 ≤ 3880; omega
  · apply DusartPrimeRowsChain.cons
    · change 3881 ≤ 3881; omega
    · change 3881 ≤ 3888; omega
    · apply DusartPrimeRowsChain.cons
      · change 3889 ≤ 3889; omega
      · change 3889 ≤ 3906; omega
      · apply DusartPrimeRowsChain.cons
        · change 3907 ≤ 3907; omega
        · change 3907 ≤ 3910; omega
        · apply DusartPrimeRowsChain.cons
          · change 3911 ≤ 3911; omega
          · change 3911 ≤ 3916; omega
          · apply DusartPrimeRowsChain.cons
            · change 3917 ≤ 3917; omega
            · change 3917 ≤ 3918; omega
            · apply DusartPrimeRowsChain.cons
              · change 3919 ≤ 3919; omega
              · change 3919 ≤ 3922; omega
              · apply DusartPrimeRowsChain.cons
                · change 3923 ≤ 3923; omega
                · change 3923 ≤ 3928; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
