import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart62

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 63 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part06_chain :
    DusartPrimeRowsChain 6971 6977 dusartPrimeRows_6637_6976_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976 : List DusartPrimeRow :=
  dusartPrimeRows_6637_6976_part01 ++ dusartPrimeRows_6637_6976_part02 ++ dusartPrimeRows_6637_6976_part03 ++ dusartPrimeRows_6637_6976_part04 ++ dusartPrimeRows_6637_6976_part05 ++ dusartPrimeRows_6637_6976_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_chain :
    DusartPrimeRowsChain 6637 6976 dusartPrimeRows_6637_6976 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part05_chain (dusartPrimeRows_6637_6976_part06_chain)))))
