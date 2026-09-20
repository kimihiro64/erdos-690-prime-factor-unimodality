import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 122 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part05_chain :
    DusartPrimeRowsChain 11257 11321 dusartPrimeRows_10939_11502_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 11257 ≤ 11257; omega
  · change 11257 ≤ 11260; omega
  · apply DusartPrimeRowsChain.cons
    · change 11261 ≤ 11261; omega
    · change 11261 ≤ 11272; omega
    · apply DusartPrimeRowsChain.cons
      · change 11273 ≤ 11273; omega
      · change 11273 ≤ 11278; omega
      · apply DusartPrimeRowsChain.cons
        · change 11279 ≤ 11279; omega
        · change 11279 ≤ 11286; omega
        · apply DusartPrimeRowsChain.cons
          · change 11287 ≤ 11287; omega
          · change 11287 ≤ 11298; omega
          · apply DusartPrimeRowsChain.cons
            · change 11299 ≤ 11299; omega
            · change 11299 ≤ 11310; omega
            · apply DusartPrimeRowsChain.cons
              · change 11311 ≤ 11311; omega
              · change 11311 ≤ 11316; omega
              · apply DusartPrimeRowsChain.cons
                · change 11317 ≤ 11317; omega
                · change 11317 ≤ 11320; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
