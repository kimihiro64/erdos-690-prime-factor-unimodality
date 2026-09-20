import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart26

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 27 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part04_chain :
    DusartPrimeRowsChain 4909 4919 dusartPrimeRows_4673_4918_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918 : List DusartPrimeRow :=
  dusartPrimeRows_4673_4918_part01 ++ dusartPrimeRows_4673_4918_part02 ++ dusartPrimeRows_4673_4918_part03 ++ dusartPrimeRows_4673_4918_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_chain :
    DusartPrimeRowsChain 4673 4918 dusartPrimeRows_4673_4918 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part03_chain (dusartPrimeRows_4673_4918_part04_chain)))
