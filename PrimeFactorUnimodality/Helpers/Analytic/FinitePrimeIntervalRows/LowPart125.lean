import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart124

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 125 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938 : List DusartPrimeRow :=
  dusartPrimeRows_10427_10938_part01 ++ dusartPrimeRows_10427_10938_part02 ++ dusartPrimeRows_10427_10938_part03 ++ dusartPrimeRows_10427_10938_part04 ++ dusartPrimeRows_10427_10938_part05 ++ dusartPrimeRows_10427_10938_part06 ++ dusartPrimeRows_10427_10938_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_chain :
    DusartPrimeRowsChain 10427 10938 dusartPrimeRows_10427_10938 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part06_chain (dusartPrimeRows_10427_10938_part07_chain))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_10938 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10426 ++ dusartPrimeRows_10427_10938

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10938_chain :
    DusartPrimeRowsChain 3275 10938 dusartPrimeRows_3275_10938 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10426_chain dusartPrimeRows_10427_10938_chain
