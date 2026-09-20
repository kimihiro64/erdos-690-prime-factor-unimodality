import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 103 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part07_chain :
    DusartPrimeRowsChain 9833 9901 dusartPrimeRows_9419_9900_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 9833 ≤ 9833; omega
  · change 9833 ≤ 9838; omega
  · apply DusartPrimeRowsChain.cons
    · change 9839 ≤ 9839; omega
    · change 9839 ≤ 9850; omega
    · apply DusartPrimeRowsChain.cons
      · change 9851 ≤ 9851; omega
      · change 9851 ≤ 9856; omega
      · apply DusartPrimeRowsChain.cons
        · change 9857 ≤ 9857; omega
        · change 9857 ≤ 9858; omega
        · apply DusartPrimeRowsChain.cons
          · change 9859 ≤ 9859; omega
          · change 9859 ≤ 9870; omega
          · apply DusartPrimeRowsChain.cons
            · change 9871 ≤ 9871; omega
            · change 9871 ≤ 9882; omega
            · apply DusartPrimeRowsChain.cons
              · change 9883 ≤ 9883; omega
              · change 9883 ≤ 9886; omega
              · apply DusartPrimeRowsChain.cons
                · change 9887 ≤ 9887; omega
                · change 9887 ≤ 9900; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
