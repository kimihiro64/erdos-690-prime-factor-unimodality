import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 76 -/

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
