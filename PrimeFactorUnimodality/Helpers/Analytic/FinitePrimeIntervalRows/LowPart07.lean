import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart06

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21727) (q := 21737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21737) (q := 21739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21739) (q := 21751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21751) (q := 21757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21757) (q := 21767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21767) (q := 21773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21773) (q := 21787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21787) (q := 21799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part11_chain :
    DusartPrimeRowsChain 21727 21799 dusartPrimeRows_20959_22026_part11 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_20959_22026_part11]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21799) (q := 21803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21803) (q := 21817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21817) (q := 21821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21821) (q := 21839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21839) (q := 21841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21841) (q := 21851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21851) (q := 21859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21859) (q := 21863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part12_chain :
    DusartPrimeRowsChain 21799 21863 dusartPrimeRows_20959_22026_part12 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_20959_22026_part12]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_20959_22026_part13]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_20959_22026_part14]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part01]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part02]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20143) (q := 20147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20147) (q := 20149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20149) (q := 20161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20161) (q := 20173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20173) (q := 20177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20177) (q := 20183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20183) (q := 20201) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20201) (q := 20219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part04_chain :
    DusartPrimeRowsChain 20143 20219 dusartPrimeRows_19937_20958_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20219) (q := 20231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20231) (q := 20233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20233) (q := 20249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20249) (q := 20261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20261) (q := 20269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20269) (q := 20287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20287) (q := 20297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20297) (q := 20323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part05_chain :
    DusartPrimeRowsChain 20219 20323 dusartPrimeRows_19937_20958_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20323) (q := 20327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20327) (q := 20333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20333) (q := 20341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20341) (q := 20347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20347) (q := 20353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20353) (q := 20357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20357) (q := 20359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20359) (q := 20369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part06_chain :
    DusartPrimeRowsChain 20323 20369 dusartPrimeRows_19937_20958_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20369) (q := 20389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20389) (q := 20393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20393) (q := 20399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20399) (q := 20407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20407) (q := 20411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20411) (q := 20431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20431) (q := 20441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20441) (q := 20443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part07_chain :
    DusartPrimeRowsChain 20369 20443 dusartPrimeRows_19937_20958_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part07]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20443) (q := 20477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20477) (q := 20479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20479) (q := 20483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20483) (q := 20507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20507) (q := 20509) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20509) (q := 20521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20521) (q := 20533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20533) (q := 20543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part08_chain :
    DusartPrimeRowsChain 20443 20543 dusartPrimeRows_19937_20958_part08 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part08]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20543) (q := 20549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20549) (q := 20551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20551) (q := 20563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20563) (q := 20593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20593) (q := 20599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20599) (q := 20611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20611) (q := 20627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20627) (q := 20639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part09_chain :
    DusartPrimeRowsChain 20543 20639 dusartPrimeRows_19937_20958_part09 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part09]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20639) (q := 20641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20641) (q := 20663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20663) (q := 20681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20681) (q := 20693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20693) (q := 20707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20707) (q := 20717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20717) (q := 20719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20719) (q := 20731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part10_chain :
    DusartPrimeRowsChain 20639 20731 dusartPrimeRows_19937_20958_part10 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part10]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20731) (q := 20743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20743) (q := 20747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20747) (q := 20749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20749) (q := 20753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20753) (q := 20759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20759) (q := 20771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20771) (q := 20773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20773) (q := 20789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part11_chain :
    DusartPrimeRowsChain 20731 20789 dusartPrimeRows_19937_20958_part11 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part11]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20789) (q := 20807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20807) (q := 20809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20809) (q := 20849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20849) (q := 20857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20857) (q := 20873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20873) (q := 20879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20879) (q := 20887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20887) (q := 20897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part12_chain :
    DusartPrimeRowsChain 20789 20897 dusartPrimeRows_19937_20958_part12 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part12]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_19937_20958_part13]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958 : List DusartPrimeRow :=
  dusartPrimeRows_19937_20958_part01 ++ dusartPrimeRows_19937_20958_part02 ++ dusartPrimeRows_19937_20958_part03 ++ dusartPrimeRows_19937_20958_part04 ++ dusartPrimeRows_19937_20958_part05 ++ dusartPrimeRows_19937_20958_part06 ++ dusartPrimeRows_19937_20958_part07 ++ dusartPrimeRows_19937_20958_part08 ++ dusartPrimeRows_19937_20958_part09 ++ dusartPrimeRows_19937_20958_part10 ++ dusartPrimeRows_19937_20958_part11 ++ dusartPrimeRows_19937_20958_part12 ++ dusartPrimeRows_19937_20958_part13

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_chain :
    DusartPrimeRowsChain 19937 20958 dusartPrimeRows_19937_20958 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_19937_20958_part12_chain (dusartPrimeRows_19937_20958_part13_chain))))))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 18959) (q := 18973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18973) (q := 18979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18979) (q := 19001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19001) (q := 19009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19009) (q := 19013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19013) (q := 19031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19031) (q := 19037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19037) (q := 19051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part01_chain :
    DusartPrimeRowsChain 18959 19051 dusartPrimeRows_18959_19936_part01 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part01]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19051) (q := 19069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19069) (q := 19073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19073) (q := 19079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19079) (q := 19081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19081) (q := 19087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19087) (q := 19121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19121) (q := 19139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19139) (q := 19141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part02_chain :
    DusartPrimeRowsChain 19051 19141 dusartPrimeRows_18959_19936_part02 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part02]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19141) (q := 19157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19157) (q := 19163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19163) (q := 19181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19181) (q := 19183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19183) (q := 19207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19207) (q := 19211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19211) (q := 19213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19213) (q := 19219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part03_chain :
    DusartPrimeRowsChain 19141 19219 dusartPrimeRows_18959_19936_part03 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19219) (q := 19231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19231) (q := 19237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19237) (q := 19249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19249) (q := 19259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19259) (q := 19267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19267) (q := 19273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19273) (q := 19289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19289) (q := 19301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part04_chain :
    DusartPrimeRowsChain 19219 19301 dusartPrimeRows_18959_19936_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19301) (q := 19309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19309) (q := 19319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19319) (q := 19333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19333) (q := 19373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19373) (q := 19379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19379) (q := 19381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19381) (q := 19387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19387) (q := 19391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part05_chain :
    DusartPrimeRowsChain 19301 19391 dusartPrimeRows_18959_19936_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19391) (q := 19403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19403) (q := 19417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19417) (q := 19421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19421) (q := 19423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19423) (q := 19427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19427) (q := 19429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19429) (q := 19433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19433) (q := 19441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part06_chain :
    DusartPrimeRowsChain 19391 19441 dusartPrimeRows_18959_19936_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19441) (q := 19447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19447) (q := 19457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19457) (q := 19463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19463) (q := 19469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19469) (q := 19471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19471) (q := 19477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19477) (q := 19483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19483) (q := 19489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part07_chain :
    DusartPrimeRowsChain 19441 19489 dusartPrimeRows_18959_19936_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part07]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19489) (q := 19501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19501) (q := 19507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19507) (q := 19531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19531) (q := 19541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19541) (q := 19543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19543) (q := 19553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19553) (q := 19559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19559) (q := 19571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part08_chain :
    DusartPrimeRowsChain 19489 19571 dusartPrimeRows_18959_19936_part08 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part08]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19571) (q := 19577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19577) (q := 19583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19583) (q := 19597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19597) (q := 19603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19603) (q := 19609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19609) (q := 19661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19661) (q := 19681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19681) (q := 19687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part09_chain :
    DusartPrimeRowsChain 19571 19687 dusartPrimeRows_18959_19936_part09 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part09]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19687) (q := 19697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19697) (q := 19699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19699) (q := 19709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19709) (q := 19717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19717) (q := 19727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19727) (q := 19739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19739) (q := 19751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19751) (q := 19753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part10_chain :
    DusartPrimeRowsChain 19687 19753 dusartPrimeRows_18959_19936_part10 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part10]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19753) (q := 19759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19759) (q := 19763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19763) (q := 19777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19777) (q := 19793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19793) (q := 19801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19801) (q := 19813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19813) (q := 19819) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19819) (q := 19841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part11_chain :
    DusartPrimeRowsChain 19753 19841 dusartPrimeRows_18959_19936_part11 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part11]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19841) (q := 19843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19843) (q := 19853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19853) (q := 19861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19861) (q := 19867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19867) (q := 19889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19889) (q := 19891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19891) (q := 19913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19913) (q := 19919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part12_chain :
    DusartPrimeRowsChain 19841 19919 dusartPrimeRows_18959_19936_part12 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part12]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19919) (q := 19927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19927) (q := 19937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part13_chain :
    DusartPrimeRowsChain 19919 19937 dusartPrimeRows_18959_19936_part13 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18959_19936_part13]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936 : List DusartPrimeRow :=
  dusartPrimeRows_18959_19936_part01 ++ dusartPrimeRows_18959_19936_part02 ++ dusartPrimeRows_18959_19936_part03 ++ dusartPrimeRows_18959_19936_part04 ++ dusartPrimeRows_18959_19936_part05 ++ dusartPrimeRows_18959_19936_part06 ++ dusartPrimeRows_18959_19936_part07 ++ dusartPrimeRows_18959_19936_part08 ++ dusartPrimeRows_18959_19936_part09 ++ dusartPrimeRows_18959_19936_part10 ++ dusartPrimeRows_18959_19936_part11 ++ dusartPrimeRows_18959_19936_part12 ++ dusartPrimeRows_18959_19936_part13

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_chain :
    DusartPrimeRowsChain 18959 19936 dusartPrimeRows_18959_19936 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_18959_19936_part12_chain (dusartPrimeRows_18959_19936_part13_chain))))))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18041) (q := 18043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18043) (q := 18047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18047) (q := 18049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18049) (q := 18059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18059) (q := 18061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18061) (q := 18077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18077) (q := 18089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18089) (q := 18097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part01_chain :
    DusartPrimeRowsChain 18041 18097 dusartPrimeRows_18041_18958_part01 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part01]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18097) (q := 18119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18119) (q := 18121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18121) (q := 18127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18127) (q := 18131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18131) (q := 18133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18133) (q := 18143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18143) (q := 18149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18149) (q := 18169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part02_chain :
    DusartPrimeRowsChain 18097 18169 dusartPrimeRows_18041_18958_part02 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part02]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18169) (q := 18181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18181) (q := 18191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18191) (q := 18199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18199) (q := 18211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18211) (q := 18217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18217) (q := 18223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18223) (q := 18229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18229) (q := 18233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part03_chain :
    DusartPrimeRowsChain 18169 18233 dusartPrimeRows_18041_18958_part03 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18233) (q := 18251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18251) (q := 18253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18253) (q := 18257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18257) (q := 18269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18269) (q := 18287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18287) (q := 18289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18289) (q := 18301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18301) (q := 18307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part04_chain :
    DusartPrimeRowsChain 18233 18307 dusartPrimeRows_18041_18958_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18307) (q := 18311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18311) (q := 18313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18313) (q := 18329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18329) (q := 18341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18341) (q := 18353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18353) (q := 18367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18367) (q := 18371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18371) (q := 18379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part05_chain :
    DusartPrimeRowsChain 18307 18379 dusartPrimeRows_18041_18958_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18379) (q := 18397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18397) (q := 18401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18401) (q := 18413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18413) (q := 18427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18427) (q := 18433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18433) (q := 18439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18439) (q := 18443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18443) (q := 18451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part06_chain :
    DusartPrimeRowsChain 18379 18451 dusartPrimeRows_18041_18958_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18451) (q := 18457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18457) (q := 18461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18461) (q := 18481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18481) (q := 18493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18493) (q := 18503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18503) (q := 18517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18517) (q := 18521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18521) (q := 18523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part07_chain :
    DusartPrimeRowsChain 18451 18523 dusartPrimeRows_18041_18958_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_18041_18958_part07]
