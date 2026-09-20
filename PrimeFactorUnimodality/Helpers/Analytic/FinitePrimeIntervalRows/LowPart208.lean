import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 208 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part05_chain :
    DusartPrimeRowsChain 22303 22397 dusartPrimeRows_22027_23158_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 22303 ≤ 22303; omega
  · change 22303 ≤ 22306; omega
  · apply DusartPrimeRowsChain.cons
    · change 22307 ≤ 22307; omega
    · change 22307 ≤ 22342; omega
    · apply DusartPrimeRowsChain.cons
      · change 22343 ≤ 22343; omega
      · change 22343 ≤ 22348; omega
      · apply DusartPrimeRowsChain.cons
        · change 22349 ≤ 22349; omega
        · change 22349 ≤ 22366; omega
        · apply DusartPrimeRowsChain.cons
          · change 22367 ≤ 22367; omega
          · change 22367 ≤ 22368; omega
          · apply DusartPrimeRowsChain.cons
            · change 22369 ≤ 22369; omega
            · change 22369 ≤ 22380; omega
            · apply DusartPrimeRowsChain.cons
              · change 22381 ≤ 22381; omega
              · change 22381 ≤ 22390; omega
              · apply DusartPrimeRowsChain.cons
                · change 22391 ≤ 22391; omega
                · change 22391 ≤ 22396; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
