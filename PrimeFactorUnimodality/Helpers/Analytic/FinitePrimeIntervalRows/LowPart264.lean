import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 264 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18379) (q := 18397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18397) (q := 18401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18401) (q := 18413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18413) (q := 18427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18427) (q := 18433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18433) (q := 18439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18439) (q := 18443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18443) (q := 18451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part06_chain :
    DusartPrimeRowsChain 18379 18451 dusartPrimeRows_18041_18958_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 18379 ≤ 18379; omega
  · change 18379 ≤ 18396; omega
  · apply DusartPrimeRowsChain.cons
    · change 18397 ≤ 18397; omega
    · change 18397 ≤ 18400; omega
    · apply DusartPrimeRowsChain.cons
      · change 18401 ≤ 18401; omega
      · change 18401 ≤ 18412; omega
      · apply DusartPrimeRowsChain.cons
        · change 18413 ≤ 18413; omega
        · change 18413 ≤ 18426; omega
        · apply DusartPrimeRowsChain.cons
          · change 18427 ≤ 18427; omega
          · change 18427 ≤ 18432; omega
          · apply DusartPrimeRowsChain.cons
            · change 18433 ≤ 18433; omega
            · change 18433 ≤ 18438; omega
            · apply DusartPrimeRowsChain.cons
              · change 18439 ≤ 18439; omega
              · change 18439 ≤ 18442; omega
              · apply DusartPrimeRowsChain.cons
                · change 18443 ≤ 18443; omega
                · change 18443 ≤ 18450; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
