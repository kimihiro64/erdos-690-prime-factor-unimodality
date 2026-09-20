import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart154

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 155 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_20958 : List DusartPrimeRow :=
  dusartPrimeRows_3275_19936 ++ dusartPrimeRows_19937_20958

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_20958_chain :
    DusartPrimeRowsChain 3275 20958 dusartPrimeRows_3275_20958 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_19936_chain dusartPrimeRows_19937_20958_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_22026 : List DusartPrimeRow :=
  dusartPrimeRows_3275_20958 ++ dusartPrimeRows_20959_22026

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_22026_chain :
    DusartPrimeRowsChain 3275 22026 dusartPrimeRows_3275_22026 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_20958_chain dusartPrimeRows_20959_22026_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_23158 : List DusartPrimeRow :=
  dusartPrimeRows_3275_22026 ++ dusartPrimeRows_22027_23158

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_23158_chain :
    DusartPrimeRowsChain 3275 23158 dusartPrimeRows_3275_23158 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_22026_chain dusartPrimeRows_22027_23158_chain
