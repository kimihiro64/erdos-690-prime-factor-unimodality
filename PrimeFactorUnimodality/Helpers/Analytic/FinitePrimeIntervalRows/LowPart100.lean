import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart99

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 100 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part11_chain :
    DusartPrimeRowsChain 15497 15527 dusartPrimeRows_14767_15526_part11 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526 : List DusartPrimeRow :=
  dusartPrimeRows_14767_15526_part01 ++ dusartPrimeRows_14767_15526_part02 ++ dusartPrimeRows_14767_15526_part03 ++ dusartPrimeRows_14767_15526_part04 ++ dusartPrimeRows_14767_15526_part05 ++ dusartPrimeRows_14767_15526_part06 ++ dusartPrimeRows_14767_15526_part07 ++ dusartPrimeRows_14767_15526_part08 ++ dusartPrimeRows_14767_15526_part09 ++ dusartPrimeRows_14767_15526_part10 ++ dusartPrimeRows_14767_15526_part11

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_chain :
    DusartPrimeRowsChain 14767 15526 dusartPrimeRows_14767_15526 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part10_chain (dusartPrimeRows_14767_15526_part11_chain))))))))))
