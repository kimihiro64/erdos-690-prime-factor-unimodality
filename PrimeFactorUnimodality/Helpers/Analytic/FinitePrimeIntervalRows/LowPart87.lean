import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 87 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part05_chain :
    DusartPrimeRowsChain 8779 8839 dusartPrimeRows_8521_8962_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 8779 ≤ 8779; omega
  · change 8779 ≤ 8782; omega
  · apply DusartPrimeRowsChain.cons
    · change 8783 ≤ 8783; omega
    · change 8783 ≤ 8802; omega
    · apply DusartPrimeRowsChain.cons
      · change 8803 ≤ 8803; omega
      · change 8803 ≤ 8806; omega
      · apply DusartPrimeRowsChain.cons
        · change 8807 ≤ 8807; omega
        · change 8807 ≤ 8818; omega
        · apply DusartPrimeRowsChain.cons
          · change 8819 ≤ 8819; omega
          · change 8819 ≤ 8820; omega
          · apply DusartPrimeRowsChain.cons
            · change 8821 ≤ 8821; omega
            · change 8821 ≤ 8830; omega
            · apply DusartPrimeRowsChain.cons
              · change 8831 ≤ 8831; omega
              · change 8831 ≤ 8836; omega
              · apply DusartPrimeRowsChain.cons
                · change 8837 ≤ 8837; omega
                · change 8837 ≤ 8838; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
