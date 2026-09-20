import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart80

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 81 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part06_chain :
    DusartPrimeRowsChain 8101 8111 dusartPrimeRows_7717_8110_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110 : List DusartPrimeRow :=
  dusartPrimeRows_7717_8110_part01 ++ dusartPrimeRows_7717_8110_part02 ++ dusartPrimeRows_7717_8110_part03 ++ dusartPrimeRows_7717_8110_part04 ++ dusartPrimeRows_7717_8110_part05 ++ dusartPrimeRows_7717_8110_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_chain :
    DusartPrimeRowsChain 7717 8110 dusartPrimeRows_7717_8110 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_7717_8110_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_7717_8110_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_7717_8110_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_7717_8110_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_7717_8110_part05_chain (dusartPrimeRows_7717_8110_part06_chain)))))
