import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart126

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 127 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21961) (q := 21977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21977) (q := 21991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21991) (q := 21997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21997) (q := 22003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22003) (q := 22013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22013) (q := 22027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part14_chain :
    DusartPrimeRowsChain 21961 22027 dusartPrimeRows_20959_22026_part14 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026 : List DusartPrimeRow :=
  dusartPrimeRows_20959_22026_part01 ++ dusartPrimeRows_20959_22026_part02 ++ dusartPrimeRows_20959_22026_part03 ++ dusartPrimeRows_20959_22026_part04 ++ dusartPrimeRows_20959_22026_part05 ++ dusartPrimeRows_20959_22026_part06 ++ dusartPrimeRows_20959_22026_part07 ++ dusartPrimeRows_20959_22026_part08 ++ dusartPrimeRows_20959_22026_part09 ++ dusartPrimeRows_20959_22026_part10 ++ dusartPrimeRows_20959_22026_part11 ++ dusartPrimeRows_20959_22026_part12 ++ dusartPrimeRows_20959_22026_part13 ++ dusartPrimeRows_20959_22026_part14

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_chain :
    DusartPrimeRowsChain 20959 22026 dusartPrimeRows_20959_22026 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part12_chain (dusartPrimeRowsChain_append dusartPrimeRows_20959_22026_part13_chain (dusartPrimeRows_20959_22026_part14_chain)))))))))))))
