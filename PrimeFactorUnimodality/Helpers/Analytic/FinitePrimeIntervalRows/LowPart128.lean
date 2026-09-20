import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 128 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part03_chain :
    DusartPrimeRowsChain 11699 11783 dusartPrimeRows_11503_12096_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 11699 ≤ 11699; omega
  · change 11699 ≤ 11700; omega
  · apply DusartPrimeRowsChain.cons
    · change 11701 ≤ 11701; omega
    · change 11701 ≤ 11716; omega
    · apply DusartPrimeRowsChain.cons
      · change 11717 ≤ 11717; omega
      · change 11717 ≤ 11718; omega
      · apply DusartPrimeRowsChain.cons
        · change 11719 ≤ 11719; omega
        · change 11719 ≤ 11730; omega
        · apply DusartPrimeRowsChain.cons
          · change 11731 ≤ 11731; omega
          · change 11731 ≤ 11742; omega
          · apply DusartPrimeRowsChain.cons
            · change 11743 ≤ 11743; omega
            · change 11743 ≤ 11776; omega
            · apply DusartPrimeRowsChain.cons
              · change 11777 ≤ 11777; omega
              · change 11777 ≤ 11778; omega
              · apply DusartPrimeRowsChain.cons
                · change 11779 ≤ 11779; omega
                · change 11779 ≤ 11782; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
