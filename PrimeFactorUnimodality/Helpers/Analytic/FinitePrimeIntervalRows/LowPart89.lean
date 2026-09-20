import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 89 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part07_chain :
    DusartPrimeRowsChain 8929 8963 dusartPrimeRows_8521_8962_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 8929 ≤ 8929; omega
  · change 8929 ≤ 8932; omega
  · apply DusartPrimeRowsChain.cons
    · change 8933 ≤ 8933; omega
    · change 8933 ≤ 8940; omega
    · apply DusartPrimeRowsChain.cons
      · change 8941 ≤ 8941; omega
      · change 8941 ≤ 8950; omega
      · apply DusartPrimeRowsChain.cons
        · change 8951 ≤ 8951; omega
        · change 8951 ≤ 8962; omega
        · apply DusartPrimeRowsChain.empty
          norm_num
