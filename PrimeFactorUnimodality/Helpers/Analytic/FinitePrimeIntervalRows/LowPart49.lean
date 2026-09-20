import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 49 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part01_chain :
    DusartPrimeRowsChain 6311 6361 dusartPrimeRows_6311_6636_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 6311 ≤ 6311; omega
  · change 6311 ≤ 6316; omega
  · apply DusartPrimeRowsChain.cons
    · change 6317 ≤ 6317; omega
    · change 6317 ≤ 6322; omega
    · apply DusartPrimeRowsChain.cons
      · change 6323 ≤ 6323; omega
      · change 6323 ≤ 6328; omega
      · apply DusartPrimeRowsChain.cons
        · change 6329 ≤ 6329; omega
        · change 6329 ≤ 6336; omega
        · apply DusartPrimeRowsChain.cons
          · change 6337 ≤ 6337; omega
          · change 6337 ≤ 6342; omega
          · apply DusartPrimeRowsChain.cons
            · change 6343 ≤ 6343; omega
            · change 6343 ≤ 6352; omega
            · apply DusartPrimeRowsChain.cons
              · change 6353 ≤ 6353; omega
              · change 6353 ≤ 6358; omega
              · apply DusartPrimeRowsChain.cons
                · change 6359 ≤ 6359; omega
                · change 6359 ≤ 6360; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
