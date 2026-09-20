import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart146

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 147 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18803) (q := 18839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18839) (q := 18859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18859) (q := 18869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18869) (q := 18899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18899) (q := 18911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18911) (q := 18913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18913) (q := 18917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18917) (q := 18919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part11_chain :
    DusartPrimeRowsChain 18803 18919 dusartPrimeRows_18041_18958_part11 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18919) (q := 18947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18947) (q := 18959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part12_chain :
    DusartPrimeRowsChain 18919 18959 dusartPrimeRows_18041_18958_part12 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958 : List DusartPrimeRow :=
  dusartPrimeRows_18041_18958_part01 ++ dusartPrimeRows_18041_18958_part02 ++ dusartPrimeRows_18041_18958_part03 ++ dusartPrimeRows_18041_18958_part04 ++ dusartPrimeRows_18041_18958_part05 ++ dusartPrimeRows_18041_18958_part06 ++ dusartPrimeRows_18041_18958_part07 ++ dusartPrimeRows_18041_18958_part08 ++ dusartPrimeRows_18041_18958_part09 ++ dusartPrimeRows_18041_18958_part10 ++ dusartPrimeRows_18041_18958_part11 ++ dusartPrimeRows_18041_18958_part12

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_chain :
    DusartPrimeRowsChain 18041 18958 dusartPrimeRows_18041_18958 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_18041_18958_part11_chain (dusartPrimeRows_18041_18958_part12_chain)))))))))))
