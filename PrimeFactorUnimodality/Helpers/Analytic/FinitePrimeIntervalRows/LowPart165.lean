import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 165 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part05_chain :
    DusartPrimeRowsChain 14411 14479 dusartPrimeRows_14051_14766_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 14411 ≤ 14411; omega
  · change 14411 ≤ 14418; omega
  · apply DusartPrimeRowsChain.cons
    · change 14419 ≤ 14419; omega
    · change 14419 ≤ 14422; omega
    · apply DusartPrimeRowsChain.cons
      · change 14423 ≤ 14423; omega
      · change 14423 ≤ 14430; omega
      · apply DusartPrimeRowsChain.cons
        · change 14431 ≤ 14431; omega
        · change 14431 ≤ 14436; omega
        · apply DusartPrimeRowsChain.cons
          · change 14437 ≤ 14437; omega
          · change 14437 ≤ 14446; omega
          · apply DusartPrimeRowsChain.cons
            · change 14447 ≤ 14447; omega
            · change 14447 ≤ 14448; omega
            · apply DusartPrimeRowsChain.cons
              · change 14449 ≤ 14449; omega
              · change 14449 ≤ 14460; omega
              · apply DusartPrimeRowsChain.cons
                · change 14461 ≤ 14461; omega
                · change 14461 ≤ 14478; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
