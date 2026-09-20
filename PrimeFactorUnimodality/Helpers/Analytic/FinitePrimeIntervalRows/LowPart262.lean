import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 262 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18233) (q := 18251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18251) (q := 18253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18253) (q := 18257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18257) (q := 18269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18269) (q := 18287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18287) (q := 18289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18289) (q := 18301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18301) (q := 18307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part04_chain :
    DusartPrimeRowsChain 18233 18307 dusartPrimeRows_18041_18958_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 18233 ≤ 18233; omega
  · change 18233 ≤ 18250; omega
  · apply DusartPrimeRowsChain.cons
    · change 18251 ≤ 18251; omega
    · change 18251 ≤ 18252; omega
    · apply DusartPrimeRowsChain.cons
      · change 18253 ≤ 18253; omega
      · change 18253 ≤ 18256; omega
      · apply DusartPrimeRowsChain.cons
        · change 18257 ≤ 18257; omega
        · change 18257 ≤ 18268; omega
        · apply DusartPrimeRowsChain.cons
          · change 18269 ≤ 18269; omega
          · change 18269 ≤ 18286; omega
          · apply DusartPrimeRowsChain.cons
            · change 18287 ≤ 18287; omega
            · change 18287 ≤ 18288; omega
            · apply DusartPrimeRowsChain.cons
              · change 18289 ≤ 18289; omega
              · change 18289 ≤ 18300; omega
              · apply DusartPrimeRowsChain.cons
                · change 18301 ≤ 18301; omega
                · change 18301 ≤ 18306; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
