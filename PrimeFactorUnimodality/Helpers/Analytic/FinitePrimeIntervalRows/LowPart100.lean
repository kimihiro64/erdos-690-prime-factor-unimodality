import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 100 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part04_chain :
    DusartPrimeRowsChain 9629 9697 dusartPrimeRows_9419_9900_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 9629 ≤ 9629; omega
  · change 9629 ≤ 9630; omega
  · apply DusartPrimeRowsChain.cons
    · change 9631 ≤ 9631; omega
    · change 9631 ≤ 9642; omega
    · apply DusartPrimeRowsChain.cons
      · change 9643 ≤ 9643; omega
      · change 9643 ≤ 9648; omega
      · apply DusartPrimeRowsChain.cons
        · change 9649 ≤ 9649; omega
        · change 9649 ≤ 9660; omega
        · apply DusartPrimeRowsChain.cons
          · change 9661 ≤ 9661; omega
          · change 9661 ≤ 9676; omega
          · apply DusartPrimeRowsChain.cons
            · change 9677 ≤ 9677; omega
            · change 9677 ≤ 9678; omega
            · apply DusartPrimeRowsChain.cons
              · change 9679 ≤ 9679; omega
              · change 9679 ≤ 9688; omega
              · apply DusartPrimeRowsChain.cons
                · change 9689 ≤ 9689; omega
                · change 9689 ≤ 9696; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
