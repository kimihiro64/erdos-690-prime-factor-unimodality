import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart64

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 65 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10939 dusartPrimeRows_10427_10938_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938 : List DusartPrimeRow :=
  dusartPrimeRows_10427_10938_part01 ++ dusartPrimeRows_10427_10938_part02 ++ dusartPrimeRows_10427_10938_part03 ++ dusartPrimeRows_10427_10938_part04 ++ dusartPrimeRows_10427_10938_part05 ++ dusartPrimeRows_10427_10938_part06 ++ dusartPrimeRows_10427_10938_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_chain :
    DusartPrimeRowsChain 10427 10938 dusartPrimeRows_10427_10938 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part06_chain (dusartPrimeRows_10427_10938_part07_chain))))))
