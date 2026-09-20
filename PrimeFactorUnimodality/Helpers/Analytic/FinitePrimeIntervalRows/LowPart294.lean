import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart293

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 294 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17989) (q := 18013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 18013) (q := 18041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part12_chain :
    DusartPrimeRowsChain 17989 18041 dusartPrimeRows_17159_18040_part12 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040 : List DusartPrimeRow :=
  dusartPrimeRows_17159_18040_part01 ++ dusartPrimeRows_17159_18040_part02 ++ dusartPrimeRows_17159_18040_part03 ++ dusartPrimeRows_17159_18040_part04 ++ dusartPrimeRows_17159_18040_part05 ++ dusartPrimeRows_17159_18040_part06 ++ dusartPrimeRows_17159_18040_part07 ++ dusartPrimeRows_17159_18040_part08 ++ dusartPrimeRows_17159_18040_part09 ++ dusartPrimeRows_17159_18040_part10 ++ dusartPrimeRows_17159_18040_part11 ++ dusartPrimeRows_17159_18040_part12

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_chain :
    DusartPrimeRowsChain 17159 18040 dusartPrimeRows_17159_18040 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part11_chain (dusartPrimeRows_17159_18040_part12_chain)))))))))))
