import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 64 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part05_chain :
    DusartPrimeRowsChain 7283 7333 dusartPrimeRows_6977_7332_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 7283 ≤ 7283; omega
  · change 7283 ≤ 7296; omega
  · apply DusartPrimeRowsChain.cons
    · change 7297 ≤ 7297; omega
    · change 7297 ≤ 7306; omega
    · apply DusartPrimeRowsChain.cons
      · change 7307 ≤ 7307; omega
      · change 7307 ≤ 7308; omega
      · apply DusartPrimeRowsChain.cons
        · change 7309 ≤ 7309; omega
        · change 7309 ≤ 7320; omega
        · apply DusartPrimeRowsChain.cons
          · change 7321 ≤ 7321; omega
          · change 7321 ≤ 7330; omega
          · apply DusartPrimeRowsChain.cons
            · change 7331 ≤ 7331; omega
            · change 7331 ≤ 7332; omega
            · apply DusartPrimeRowsChain.empty
              norm_num
