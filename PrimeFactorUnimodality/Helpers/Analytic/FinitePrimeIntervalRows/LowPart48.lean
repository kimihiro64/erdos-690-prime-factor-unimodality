import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 48 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part05_chain :
    DusartPrimeRowsChain 6271 6311 dusartPrimeRows_6007_6310_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 6271 ≤ 6271; omega
  · change 6271 ≤ 6276; omega
  · apply DusartPrimeRowsChain.cons
    · change 6277 ≤ 6277; omega
    · change 6277 ≤ 6286; omega
    · apply DusartPrimeRowsChain.cons
      · change 6287 ≤ 6287; omega
      · change 6287 ≤ 6298; omega
      · apply DusartPrimeRowsChain.cons
        · change 6299 ≤ 6299; omega
        · change 6299 ≤ 6300; omega
        · apply DusartPrimeRowsChain.cons
          · change 6301 ≤ 6301; omega
          · change 6301 ≤ 6310; omega
          · apply DusartPrimeRowsChain.empty
            norm_num
