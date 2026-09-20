import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart46

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 47 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18523) (q := 18539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18539) (q := 18541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18541) (q := 18553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18553) (q := 18583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18583) (q := 18587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18587) (q := 18593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18593) (q := 18617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18617) (q := 18637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part08_chain :
    DusartPrimeRowsChain 18523 18637 dusartPrimeRows_18041_18958_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18637) (q := 18661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18661) (q := 18671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18671) (q := 18679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18679) (q := 18691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18691) (q := 18701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18701) (q := 18713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18713) (q := 18719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18719) (q := 18731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part09_chain :
    DusartPrimeRowsChain 18637 18731 dusartPrimeRows_18041_18958_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18731) (q := 18743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18743) (q := 18749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18749) (q := 18757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18757) (q := 18773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18773) (q := 18787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18787) (q := 18793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18793) (q := 18797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18797) (q := 18803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part10_chain :
    DusartPrimeRowsChain 18731 18803 dusartPrimeRows_18041_18958_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
