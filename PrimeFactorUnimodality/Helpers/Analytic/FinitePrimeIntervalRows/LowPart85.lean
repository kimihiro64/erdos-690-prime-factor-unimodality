import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 85 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part03_chain :
    DusartPrimeRowsChain 8663 8713 dusartPrimeRows_8521_8962_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 8663 ≤ 8663; omega
  · change 8663 ≤ 8668; omega
  · apply DusartPrimeRowsChain.cons
    · change 8669 ≤ 8669; omega
    · change 8669 ≤ 8676; omega
    · apply DusartPrimeRowsChain.cons
      · change 8677 ≤ 8677; omega
      · change 8677 ≤ 8680; omega
      · apply DusartPrimeRowsChain.cons
        · change 8681 ≤ 8681; omega
        · change 8681 ≤ 8688; omega
        · apply DusartPrimeRowsChain.cons
          · change 8689 ≤ 8689; omega
          · change 8689 ≤ 8692; omega
          · apply DusartPrimeRowsChain.cons
            · change 8693 ≤ 8693; omega
            · change 8693 ≤ 8698; omega
            · apply DusartPrimeRowsChain.cons
              · change 8699 ≤ 8699; omega
              · change 8699 ≤ 8706; omega
              · apply DusartPrimeRowsChain.cons
                · change 8707 ≤ 8707; omega
                · change 8707 ≤ 8712; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
