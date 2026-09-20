import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart56

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 57 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part05_chain :
    DusartPrimeRowsChain 6599 6637 dusartPrimeRows_6311_6636_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636 : List DusartPrimeRow :=
  dusartPrimeRows_6311_6636_part01 ++ dusartPrimeRows_6311_6636_part02 ++ dusartPrimeRows_6311_6636_part03 ++ dusartPrimeRows_6311_6636_part04 ++ dusartPrimeRows_6311_6636_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_chain :
    DusartPrimeRowsChain 6311 6636 dusartPrimeRows_6311_6636 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part04_chain (dusartPrimeRows_6311_6636_part05_chain))))
