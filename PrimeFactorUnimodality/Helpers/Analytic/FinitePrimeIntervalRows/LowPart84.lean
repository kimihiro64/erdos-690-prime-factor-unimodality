import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 84 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part02_chain :
    DusartPrimeRowsChain 8597 8663 dusartPrimeRows_8521_8962_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 8597 ≤ 8597; omega
  · change 8597 ≤ 8598; omega
  · apply DusartPrimeRowsChain.cons
    · change 8599 ≤ 8599; omega
    · change 8599 ≤ 8608; omega
    · apply DusartPrimeRowsChain.cons
      · change 8609 ≤ 8609; omega
      · change 8609 ≤ 8622; omega
      · apply DusartPrimeRowsChain.cons
        · change 8623 ≤ 8623; omega
        · change 8623 ≤ 8626; omega
        · apply DusartPrimeRowsChain.cons
          · change 8627 ≤ 8627; omega
          · change 8627 ≤ 8628; omega
          · apply DusartPrimeRowsChain.cons
            · change 8629 ≤ 8629; omega
            · change 8629 ≤ 8640; omega
            · apply DusartPrimeRowsChain.cons
              · change 8641 ≤ 8641; omega
              · change 8641 ≤ 8646; omega
              · apply DusartPrimeRowsChain.cons
                · change 8647 ≤ 8647; omega
                · change 8647 ≤ 8662; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
