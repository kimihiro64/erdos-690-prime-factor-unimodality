import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart31

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 32 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166 : List DusartPrimeRow :=
  dusartPrimeRows_4919_5166_part01 ++ dusartPrimeRows_4919_5166_part02 ++ dusartPrimeRows_4919_5166_part03 ++ dusartPrimeRows_4919_5166_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_chain :
    DusartPrimeRowsChain 4919 5166 dusartPrimeRows_4919_5166 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part03_chain (dusartPrimeRows_4919_5166_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_5166 : List DusartPrimeRow :=
  dusartPrimeRows_3275_4918 ++ dusartPrimeRows_4919_5166

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5166_chain :
    DusartPrimeRowsChain 3275 5166 dusartPrimeRows_3275_5166 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_4918_chain dusartPrimeRows_4919_5166_chain
