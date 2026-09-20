import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 35 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part01_chain :
    DusartPrimeRowsChain 5437 5501 dusartPrimeRows_5437_5710_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 5437 ≤ 5437; omega
  · change 5437 ≤ 5440; omega
  · apply DusartPrimeRowsChain.cons
    · change 5441 ≤ 5441; omega
    · change 5441 ≤ 5442; omega
    · apply DusartPrimeRowsChain.cons
      · change 5443 ≤ 5443; omega
      · change 5443 ≤ 5448; omega
      · apply DusartPrimeRowsChain.cons
        · change 5449 ≤ 5449; omega
        · change 5449 ≤ 5470; omega
        · apply DusartPrimeRowsChain.cons
          · change 5471 ≤ 5471; omega
          · change 5471 ≤ 5476; omega
          · apply DusartPrimeRowsChain.cons
            · change 5477 ≤ 5477; omega
            · change 5477 ≤ 5478; omega
            · apply DusartPrimeRowsChain.cons
              · change 5479 ≤ 5479; omega
              · change 5479 ≤ 5482; omega
              · apply DusartPrimeRowsChain.cons
                · change 5483 ≤ 5483; omega
                · change 5483 ≤ 5500; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
