import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart08

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 09 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3803 dusartPrimeRows_3275_3802_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802 : List DusartPrimeRow :=
  dusartPrimeRows_3275_3802_part01 ++ dusartPrimeRows_3275_3802_part02 ++ dusartPrimeRows_3275_3802_part03 ++ dusartPrimeRows_3275_3802_part04 ++ dusartPrimeRows_3275_3802_part05 ++ dusartPrimeRows_3275_3802_part06 ++ dusartPrimeRows_3275_3802_part07 ++ dusartPrimeRows_3275_3802_part08 ++ dusartPrimeRows_3275_3802_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_chain :
    DusartPrimeRowsChain 3275 3802 dusartPrimeRows_3275_3802 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part08_chain (dusartPrimeRows_3275_3802_part09_chain))))))))
