import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart159

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 160 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13367 dusartPrimeRows_12713_13366_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366 : List DusartPrimeRow :=
  dusartPrimeRows_12713_13366_part01 ++ dusartPrimeRows_12713_13366_part02 ++ dusartPrimeRows_12713_13366_part03 ++ dusartPrimeRows_12713_13366_part04 ++ dusartPrimeRows_12713_13366_part05 ++ dusartPrimeRows_12713_13366_part06 ++ dusartPrimeRows_12713_13366_part07 ++ dusartPrimeRows_12713_13366_part08 ++ dusartPrimeRows_12713_13366_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_chain :
    DusartPrimeRowsChain 12713 13366 dusartPrimeRows_12713_13366 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part08_chain (dusartPrimeRows_12713_13366_part09_chain))))))))
