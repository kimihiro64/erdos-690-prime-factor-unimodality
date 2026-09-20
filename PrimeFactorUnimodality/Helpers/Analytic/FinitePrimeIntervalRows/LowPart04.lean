import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 04 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part04_chain :
    DusartPrimeRowsChain 3467 3533 dusartPrimeRows_3275_3802_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 3467 ≤ 3467; omega
  · change 3467 ≤ 3468; omega
  · apply DusartPrimeRowsChain.cons
    · change 3469 ≤ 3469; omega
    · change 3469 ≤ 3490; omega
    · apply DusartPrimeRowsChain.cons
      · change 3491 ≤ 3491; omega
      · change 3491 ≤ 3498; omega
      · apply DusartPrimeRowsChain.cons
        · change 3499 ≤ 3499; omega
        · change 3499 ≤ 3510; omega
        · apply DusartPrimeRowsChain.cons
          · change 3511 ≤ 3511; omega
          · change 3511 ≤ 3516; omega
          · apply DusartPrimeRowsChain.cons
            · change 3517 ≤ 3517; omega
            · change 3517 ≤ 3526; omega
            · apply DusartPrimeRowsChain.cons
              · change 3527 ≤ 3527; omega
              · change 3527 ≤ 3528; omega
              · apply DusartPrimeRowsChain.cons
                · change 3529 ≤ 3529; omega
                · change 3529 ≤ 3532; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
