import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart111

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 112 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158 : List DusartPrimeRow :=
  dusartPrimeRows_16319_17158_part01 ++ dusartPrimeRows_16319_17158_part02 ++ dusartPrimeRows_16319_17158_part03 ++ dusartPrimeRows_16319_17158_part04 ++ dusartPrimeRows_16319_17158_part05 ++ dusartPrimeRows_16319_17158_part06 ++ dusartPrimeRows_16319_17158_part07 ++ dusartPrimeRows_16319_17158_part08 ++ dusartPrimeRows_16319_17158_part09 ++ dusartPrimeRows_16319_17158_part10 ++ dusartPrimeRows_16319_17158_part11

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_chain :
    DusartPrimeRowsChain 16319 17158 dusartPrimeRows_16319_17158 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_16319_17158_part10_chain (dusartPrimeRows_16319_17158_part11_chain))))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part01_chain :
    DusartPrimeRowsChain 22027 22079 dusartPrimeRows_22027_23158_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
