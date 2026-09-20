import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 05 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part05_chain :
    DusartPrimeRowsChain 3533 3583 dusartPrimeRows_3275_3802_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 3533 ≤ 3533; omega
  · change 3533 ≤ 3538; omega
  · apply DusartPrimeRowsChain.cons
    · change 3539 ≤ 3539; omega
    · change 3539 ≤ 3540; omega
    · apply DusartPrimeRowsChain.cons
      · change 3541 ≤ 3541; omega
      · change 3541 ≤ 3546; omega
      · apply DusartPrimeRowsChain.cons
        · change 3547 ≤ 3547; omega
        · change 3547 ≤ 3556; omega
        · apply DusartPrimeRowsChain.cons
          · change 3557 ≤ 3557; omega
          · change 3557 ≤ 3558; omega
          · apply DusartPrimeRowsChain.cons
            · change 3559 ≤ 3559; omega
            · change 3559 ≤ 3570; omega
            · apply DusartPrimeRowsChain.cons
              · change 3571 ≤ 3571; omega
              · change 3571 ≤ 3580; omega
              · apply DusartPrimeRowsChain.cons
                · change 3581 ≤ 3581; omega
                · change 3581 ≤ 3582; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
