import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 273 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17327) (q := 17333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17333) (q := 17341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17341) (q := 17351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17351) (q := 17359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17359) (q := 17377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17377) (q := 17383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17383) (q := 17387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17387) (q := 17389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part03_chain :
    DusartPrimeRowsChain 17327 17389 dusartPrimeRows_17159_18040_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 17327 ≤ 17327; omega
  · change 17327 ≤ 17332; omega
  · apply DusartPrimeRowsChain.cons
    · change 17333 ≤ 17333; omega
    · change 17333 ≤ 17340; omega
    · apply DusartPrimeRowsChain.cons
      · change 17341 ≤ 17341; omega
      · change 17341 ≤ 17350; omega
      · apply DusartPrimeRowsChain.cons
        · change 17351 ≤ 17351; omega
        · change 17351 ≤ 17358; omega
        · apply DusartPrimeRowsChain.cons
          · change 17359 ≤ 17359; omega
          · change 17359 ≤ 17376; omega
          · apply DusartPrimeRowsChain.cons
            · change 17377 ≤ 17377; omega
            · change 17377 ≤ 17382; omega
            · apply DusartPrimeRowsChain.cons
              · change 17383 ≤ 17383; omega
              · change 17383 ≤ 17386; omega
              · apply DusartPrimeRowsChain.cons
                · change 17387 ≤ 17387; omega
                · change 17387 ≤ 17388; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
