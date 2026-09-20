import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 164 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part04_chain :
    DusartPrimeRowsChain 14327 14411 dusartPrimeRows_14051_14766_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 14327 ≤ 14327; omega
  · change 14327 ≤ 14340; omega
  · apply DusartPrimeRowsChain.cons
    · change 14341 ≤ 14341; omega
    · change 14341 ≤ 14346; omega
    · apply DusartPrimeRowsChain.cons
      · change 14347 ≤ 14347; omega
      · change 14347 ≤ 14368; omega
      · apply DusartPrimeRowsChain.cons
        · change 14369 ≤ 14369; omega
        · change 14369 ≤ 14386; omega
        · apply DusartPrimeRowsChain.cons
          · change 14387 ≤ 14387; omega
          · change 14387 ≤ 14388; omega
          · apply DusartPrimeRowsChain.cons
            · change 14389 ≤ 14389; omega
            · change 14389 ≤ 14400; omega
            · apply DusartPrimeRowsChain.cons
              · change 14401 ≤ 14401; omega
              · change 14401 ≤ 14406; omega
              · apply DusartPrimeRowsChain.cons
                · change 14407 ≤ 14407; omega
                · change 14407 ≤ 14410; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
