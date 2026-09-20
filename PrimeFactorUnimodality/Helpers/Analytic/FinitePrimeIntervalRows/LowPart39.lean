import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 39 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part05_chain :
    DusartPrimeRowsChain 5693 5711 dusartPrimeRows_5437_5710_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
