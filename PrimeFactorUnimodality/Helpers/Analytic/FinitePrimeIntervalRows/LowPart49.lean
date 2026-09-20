import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart48

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 49 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part07_chain :
    DusartPrimeRowsChain 8929 8963 dusartPrimeRows_8521_8962_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962 : List DusartPrimeRow :=
  dusartPrimeRows_8521_8962_part01 ++ dusartPrimeRows_8521_8962_part02 ++ dusartPrimeRows_8521_8962_part03 ++ dusartPrimeRows_8521_8962_part04 ++ dusartPrimeRows_8521_8962_part05 ++ dusartPrimeRows_8521_8962_part06 ++ dusartPrimeRows_8521_8962_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_chain :
    DusartPrimeRowsChain 8521 8962 dusartPrimeRows_8521_8962 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_8521_8962_part06_chain (dusartPrimeRows_8521_8962_part07_chain))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_8962 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8520 ++ dusartPrimeRows_8521_8962

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8962_chain :
    DusartPrimeRowsChain 3275 8962 dusartPrimeRows_3275_8962 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8520_chain dusartPrimeRows_8521_8962_chain
