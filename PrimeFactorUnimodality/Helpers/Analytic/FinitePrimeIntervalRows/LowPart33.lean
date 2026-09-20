import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 33 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part03_chain :
    DusartPrimeRowsChain 5309 5399 dusartPrimeRows_5167_5436_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 5309 ≤ 5309; omega
  · change 5309 ≤ 5322; omega
  · apply DusartPrimeRowsChain.cons
    · change 5323 ≤ 5323; omega
    · change 5323 ≤ 5332; omega
    · apply DusartPrimeRowsChain.cons
      · change 5333 ≤ 5333; omega
      · change 5333 ≤ 5346; omega
      · apply DusartPrimeRowsChain.cons
        · change 5347 ≤ 5347; omega
        · change 5347 ≤ 5350; omega
        · apply DusartPrimeRowsChain.cons
          · change 5351 ≤ 5351; omega
          · change 5351 ≤ 5380; omega
          · apply DusartPrimeRowsChain.cons
            · change 5381 ≤ 5381; omega
            · change 5381 ≤ 5386; omega
            · apply DusartPrimeRowsChain.cons
              · change 5387 ≤ 5387; omega
              · change 5387 ≤ 5392; omega
              · apply DusartPrimeRowsChain.cons
                · change 5393 ≤ 5393; omega
                · change 5393 ≤ 5398; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
