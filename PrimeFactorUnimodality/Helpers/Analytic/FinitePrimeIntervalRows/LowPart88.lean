import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 88 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part06_chain :
    DusartPrimeRowsChain 8839 8929 dusartPrimeRows_8521_8962_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 8839 ≤ 8839; omega
  · change 8839 ≤ 8848; omega
  · apply DusartPrimeRowsChain.cons
    · change 8849 ≤ 8849; omega
    · change 8849 ≤ 8860; omega
    · apply DusartPrimeRowsChain.cons
      · change 8861 ≤ 8861; omega
      · change 8861 ≤ 8862; omega
      · apply DusartPrimeRowsChain.cons
        · change 8863 ≤ 8863; omega
        · change 8863 ≤ 8866; omega
        · apply DusartPrimeRowsChain.cons
          · change 8867 ≤ 8867; omega
          · change 8867 ≤ 8886; omega
          · apply DusartPrimeRowsChain.cons
            · change 8887 ≤ 8887; omega
            · change 8887 ≤ 8892; omega
            · apply DusartPrimeRowsChain.cons
              · change 8893 ≤ 8893; omega
              · change 8893 ≤ 8922; omega
              · apply DusartPrimeRowsChain.cons
                · change 8923 ≤ 8923; omega
                · change 8923 ≤ 8928; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
