import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 123 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part06_chain :
    DusartPrimeRowsChain 11321 11411 dusartPrimeRows_10939_11502_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 11321 ≤ 11321; omega
  · change 11321 ≤ 11328; omega
  · apply DusartPrimeRowsChain.cons
    · change 11329 ≤ 11329; omega
    · change 11329 ≤ 11350; omega
    · apply DusartPrimeRowsChain.cons
      · change 11351 ≤ 11351; omega
      · change 11351 ≤ 11352; omega
      · apply DusartPrimeRowsChain.cons
        · change 11353 ≤ 11353; omega
        · change 11353 ≤ 11368; omega
        · apply DusartPrimeRowsChain.cons
          · change 11369 ≤ 11369; omega
          · change 11369 ≤ 11382; omega
          · apply DusartPrimeRowsChain.cons
            · change 11383 ≤ 11383; omega
            · change 11383 ≤ 11392; omega
            · apply DusartPrimeRowsChain.cons
              · change 11393 ≤ 11393; omega
              · change 11393 ≤ 11398; omega
              · apply DusartPrimeRowsChain.cons
                · change 11399 ≤ 11399; omega
                · change 11399 ≤ 11410; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
