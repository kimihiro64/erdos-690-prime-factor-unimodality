import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart41

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 42 -/

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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710 : List DusartPrimeRow :=
  dusartPrimeRows_5437_5710_part01 ++ dusartPrimeRows_5437_5710_part02 ++ dusartPrimeRows_5437_5710_part03 ++ dusartPrimeRows_5437_5710_part04 ++ dusartPrimeRows_5437_5710_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_chain :
    DusartPrimeRowsChain 5437 5710 dusartPrimeRows_5437_5710 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part04_chain (dusartPrimeRows_5437_5710_part05_chain))))
