import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart40

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 41 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21863) (q := 21871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21871) (q := 21881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21881) (q := 21893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21893) (q := 21911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21911) (q := 21929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21929) (q := 21937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21937) (q := 21943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21943) (q := 21961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part13_chain :
    DusartPrimeRowsChain 21863 21961 dusartPrimeRows_20959_22026_part13 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19937) (q := 19949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19949) (q := 19961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19961) (q := 19963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19963) (q := 19973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19973) (q := 19979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19979) (q := 19991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19991) (q := 19993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19993) (q := 19997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part01_chain :
    DusartPrimeRowsChain 19937 19997 dusartPrimeRows_19937_20958_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19997) (q := 20011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20011) (q := 20021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20021) (q := 20023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20023) (q := 20029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20029) (q := 20047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20047) (q := 20051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20051) (q := 20063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20063) (q := 20071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part02_chain :
    DusartPrimeRowsChain 19997 20071 dusartPrimeRows_19937_20958_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20071) (q := 20089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20089) (q := 20101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20101) (q := 20107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20107) (q := 20113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20113) (q := 20117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20117) (q := 20123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20123) (q := 20129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20129) (q := 20143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part03_chain :
    DusartPrimeRowsChain 20071 20143 dusartPrimeRows_19937_20958_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
