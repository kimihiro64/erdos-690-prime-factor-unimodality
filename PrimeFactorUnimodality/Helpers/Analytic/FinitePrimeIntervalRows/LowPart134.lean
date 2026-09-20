import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart133

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 134 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20897) (q := 20899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20899) (q := 20903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20903) (q := 20921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20921) (q := 20929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20929) (q := 20939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20939) (q := 20947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20947) (q := 20959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part13_chain :
    DusartPrimeRowsChain 20897 20959 dusartPrimeRows_19937_20958_part13 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958 : List DusartPrimeRow :=
  dusartPrimeRows_19937_20958_part01 ++ dusartPrimeRows_19937_20958_part02 ++ dusartPrimeRows_19937_20958_part03 ++ dusartPrimeRows_19937_20958_part04 ++ dusartPrimeRows_19937_20958_part05 ++ dusartPrimeRows_19937_20958_part06 ++ dusartPrimeRows_19937_20958_part07 ++ dusartPrimeRows_19937_20958_part08 ++ dusartPrimeRows_19937_20958_part09 ++ dusartPrimeRows_19937_20958_part10 ++ dusartPrimeRows_19937_20958_part11 ++ dusartPrimeRows_19937_20958_part12 ++ dusartPrimeRows_19937_20958_part13

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_chain :
    DusartPrimeRowsChain 19937 20958 dusartPrimeRows_19937_20958 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part12_chain (dusartPrimeRows_19937_20958_part13_chain))))))))))))
