import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart179

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 180 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part10_chain :
    DusartPrimeRowsChain 14759 14767 dusartPrimeRows_14051_14766_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766 : List DusartPrimeRow :=
  dusartPrimeRows_14051_14766_part01 ++ dusartPrimeRows_14051_14766_part02 ++ dusartPrimeRows_14051_14766_part03 ++ dusartPrimeRows_14051_14766_part04 ++ dusartPrimeRows_14051_14766_part05 ++ dusartPrimeRows_14051_14766_part06 ++ dusartPrimeRows_14051_14766_part07 ++ dusartPrimeRows_14051_14766_part08 ++ dusartPrimeRows_14051_14766_part09 ++ dusartPrimeRows_14051_14766_part10

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_chain :
    DusartPrimeRowsChain 14051 14766 dusartPrimeRows_14051_14766 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part09_chain (dusartPrimeRows_14051_14766_part10_chain)))))))))
