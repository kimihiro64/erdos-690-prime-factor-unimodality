import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart119

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 120 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158 : List DusartPrimeRow :=
  dusartPrimeRows_22027_23158_part01 ++ dusartPrimeRows_22027_23158_part02 ++ dusartPrimeRows_22027_23158_part03 ++ dusartPrimeRows_22027_23158_part04 ++ dusartPrimeRows_22027_23158_part05 ++ dusartPrimeRows_22027_23158_part06 ++ dusartPrimeRows_22027_23158_part07 ++ dusartPrimeRows_22027_23158_part08 ++ dusartPrimeRows_22027_23158_part09 ++ dusartPrimeRows_22027_23158_part10 ++ dusartPrimeRows_22027_23158_part11 ++ dusartPrimeRows_22027_23158_part12 ++ dusartPrimeRows_22027_23158_part13 ++ dusartPrimeRows_22027_23158_part14 ++ dusartPrimeRows_22027_23158_part15

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_chain :
    DusartPrimeRowsChain 22027 23158 dusartPrimeRows_22027_23158 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part12_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part13_chain (dusartPrimeRowsChain_append dusartPrimeRows_22027_23158_part14_chain (dusartPrimeRows_22027_23158_part15_chain))))))))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 20959) (q := 20963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20963) (q := 20981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20981) (q := 20983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20983) (q := 21001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21001) (q := 21011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21011) (q := 21013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21013) (q := 21017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21017) (q := 21019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part01_chain :
    DusartPrimeRowsChain 20959 21019 dusartPrimeRows_20959_22026_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
