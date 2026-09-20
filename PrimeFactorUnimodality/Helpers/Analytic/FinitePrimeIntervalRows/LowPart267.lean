import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 267 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18637) (q := 18661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18661) (q := 18671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18671) (q := 18679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18679) (q := 18691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18691) (q := 18701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18701) (q := 18713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18713) (q := 18719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18719) (q := 18731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part09_chain :
    DusartPrimeRowsChain 18637 18731 dusartPrimeRows_18041_18958_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 18637 ≤ 18637; omega
  · change 18637 ≤ 18660; omega
  · apply DusartPrimeRowsChain.cons
    · change 18661 ≤ 18661; omega
    · change 18661 ≤ 18670; omega
    · apply DusartPrimeRowsChain.cons
      · change 18671 ≤ 18671; omega
      · change 18671 ≤ 18678; omega
      · apply DusartPrimeRowsChain.cons
        · change 18679 ≤ 18679; omega
        · change 18679 ≤ 18690; omega
        · apply DusartPrimeRowsChain.cons
          · change 18691 ≤ 18691; omega
          · change 18691 ≤ 18700; omega
          · apply DusartPrimeRowsChain.cons
            · change 18701 ≤ 18701; omega
            · change 18701 ≤ 18712; omega
            · apply DusartPrimeRowsChain.cons
              · change 18713 ≤ 18713; omega
              · change 18713 ≤ 18718; omega
              · apply DusartPrimeRowsChain.cons
                · change 18719 ≤ 18719; omega
                · change 18719 ≤ 18730; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
