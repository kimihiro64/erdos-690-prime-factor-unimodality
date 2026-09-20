import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 83 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part01_chain :
    DusartPrimeRowsChain 8521 8597 dusartPrimeRows_8521_8962_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 8521 ≤ 8521; omega
  · change 8521 ≤ 8526; omega
  · apply DusartPrimeRowsChain.cons
    · change 8527 ≤ 8527; omega
    · change 8527 ≤ 8536; omega
    · apply DusartPrimeRowsChain.cons
      · change 8537 ≤ 8537; omega
      · change 8537 ≤ 8538; omega
      · apply DusartPrimeRowsChain.cons
        · change 8539 ≤ 8539; omega
        · change 8539 ≤ 8542; omega
        · apply DusartPrimeRowsChain.cons
          · change 8543 ≤ 8543; omega
          · change 8543 ≤ 8562; omega
          · apply DusartPrimeRowsChain.cons
            · change 8563 ≤ 8563; omega
            · change 8563 ≤ 8572; omega
            · apply DusartPrimeRowsChain.cons
              · change 8573 ≤ 8573; omega
              · change 8573 ≤ 8580; omega
              · apply DusartPrimeRowsChain.cons
                · change 8581 ≤ 8581; omega
                · change 8581 ≤ 8596; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
