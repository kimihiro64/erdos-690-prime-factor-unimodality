import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 06 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part06_chain :
    DusartPrimeRowsChain 3583 3643 dusartPrimeRows_3275_3802_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 3583 ≤ 3583; omega
  · change 3583 ≤ 3592; omega
  · apply DusartPrimeRowsChain.cons
    · change 3593 ≤ 3593; omega
    · change 3593 ≤ 3606; omega
    · apply DusartPrimeRowsChain.cons
      · change 3607 ≤ 3607; omega
      · change 3607 ≤ 3612; omega
      · apply DusartPrimeRowsChain.cons
        · change 3613 ≤ 3613; omega
        · change 3613 ≤ 3616; omega
        · apply DusartPrimeRowsChain.cons
          · change 3617 ≤ 3617; omega
          · change 3617 ≤ 3622; omega
          · apply DusartPrimeRowsChain.cons
            · change 3623 ≤ 3623; omega
            · change 3623 ≤ 3630; omega
            · apply DusartPrimeRowsChain.cons
              · change 3631 ≤ 3631; omega
              · change 3631 ≤ 3636; omega
              · apply DusartPrimeRowsChain.cons
                · change 3637 ≤ 3637; omega
                · change 3637 ≤ 3642; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
