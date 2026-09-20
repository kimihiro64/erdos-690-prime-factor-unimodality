import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart23

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 24 -/

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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part01_chain :
    DusartPrimeRowsChain 12097 12157 dusartPrimeRows_12097_12712_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part02_chain :
    DusartPrimeRowsChain 12157 12241 dusartPrimeRows_12097_12712_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part03_chain :
    DusartPrimeRowsChain 12241 12301 dusartPrimeRows_12097_12712_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12391 dusartPrimeRows_12097_12712_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12457 dusartPrimeRows_12097_12712_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
