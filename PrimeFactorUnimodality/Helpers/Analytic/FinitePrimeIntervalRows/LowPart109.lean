import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart108

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 109 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900 : List DusartPrimeRow :=
  dusartPrimeRows_9419_9900_part01 ++ dusartPrimeRows_9419_9900_part02 ++ dusartPrimeRows_9419_9900_part03 ++ dusartPrimeRows_9419_9900_part04 ++ dusartPrimeRows_9419_9900_part05 ++ dusartPrimeRows_9419_9900_part06 ++ dusartPrimeRows_9419_9900_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_chain :
    DusartPrimeRowsChain 9419 9900 dusartPrimeRows_9419_9900 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_9419_9900_part06_chain (dusartPrimeRows_9419_9900_part07_chain))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_9900 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9418 ++ dusartPrimeRows_9419_9900

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_9900_chain :
    DusartPrimeRowsChain 3275 9900 dusartPrimeRows_3275_9900 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9418_chain dusartPrimeRows_9419_9900_chain
