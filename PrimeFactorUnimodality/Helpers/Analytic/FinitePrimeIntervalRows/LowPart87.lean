import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart86

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 87 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part06_chain :
    DusartPrimeRowsChain 8501 8521 dusartPrimeRows_8111_8520_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520 : List DusartPrimeRow :=
  dusartPrimeRows_8111_8520_part01 ++ dusartPrimeRows_8111_8520_part02 ++ dusartPrimeRows_8111_8520_part03 ++ dusartPrimeRows_8111_8520_part04 ++ dusartPrimeRows_8111_8520_part05 ++ dusartPrimeRows_8111_8520_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_chain :
    DusartPrimeRowsChain 8111 8520 dusartPrimeRows_8111_8520 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_8111_8520_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_8111_8520_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_8111_8520_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_8111_8520_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_8111_8520_part05_chain (dusartPrimeRows_8111_8520_part06_chain)))))
