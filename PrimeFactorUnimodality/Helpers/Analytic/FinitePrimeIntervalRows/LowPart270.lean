import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart269

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 270 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19919) (q := 19927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19927) (q := 19937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part13_chain :
    DusartPrimeRowsChain 19919 19937 dusartPrimeRows_18959_19936_part13 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936 : List DusartPrimeRow :=
  dusartPrimeRows_18959_19936_part01 ++ dusartPrimeRows_18959_19936_part02 ++ dusartPrimeRows_18959_19936_part03 ++ dusartPrimeRows_18959_19936_part04 ++ dusartPrimeRows_18959_19936_part05 ++ dusartPrimeRows_18959_19936_part06 ++ dusartPrimeRows_18959_19936_part07 ++ dusartPrimeRows_18959_19936_part08 ++ dusartPrimeRows_18959_19936_part09 ++ dusartPrimeRows_18959_19936_part10 ++ dusartPrimeRows_18959_19936_part11 ++ dusartPrimeRows_18959_19936_part12 ++ dusartPrimeRows_18959_19936_part13

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_chain :
    DusartPrimeRowsChain 18959 19936 dusartPrimeRows_18959_19936 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part12_chain (dusartPrimeRows_18959_19936_part13_chain))))))))))))
