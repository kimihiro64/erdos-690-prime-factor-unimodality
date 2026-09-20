import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart36

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 37 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436 : List DusartPrimeRow :=
  dusartPrimeRows_5167_5436_part01 ++ dusartPrimeRows_5167_5436_part02 ++ dusartPrimeRows_5167_5436_part03 ++ dusartPrimeRows_5167_5436_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_chain :
    DusartPrimeRowsChain 5167 5436 dusartPrimeRows_5167_5436 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part03_chain (dusartPrimeRows_5167_5436_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_5436 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5166 ++ dusartPrimeRows_5167_5436

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5436_chain :
    DusartPrimeRowsChain 3275 5436 dusartPrimeRows_3275_5436 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5166_chain dusartPrimeRows_5167_5436_chain
