import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart73

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 74 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part08_chain :
    DusartPrimeRowsChain 12049 12097 dusartPrimeRows_11503_12096_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096 : List DusartPrimeRow :=
  dusartPrimeRows_11503_12096_part01 ++ dusartPrimeRows_11503_12096_part02 ++ dusartPrimeRows_11503_12096_part03 ++ dusartPrimeRows_11503_12096_part04 ++ dusartPrimeRows_11503_12096_part05 ++ dusartPrimeRows_11503_12096_part06 ++ dusartPrimeRows_11503_12096_part07 ++ dusartPrimeRows_11503_12096_part08

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_chain :
    DusartPrimeRowsChain 11503 12096 dusartPrimeRows_11503_12096 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part07_chain (dusartPrimeRows_11503_12096_part08_chain)))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_12096 : List DusartPrimeRow :=
  dusartPrimeRows_3275_11502 ++ dusartPrimeRows_11503_12096

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12096_chain :
    DusartPrimeRowsChain 3275 12096 dusartPrimeRows_3275_12096 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_11502_chain dusartPrimeRows_11503_12096_chain
