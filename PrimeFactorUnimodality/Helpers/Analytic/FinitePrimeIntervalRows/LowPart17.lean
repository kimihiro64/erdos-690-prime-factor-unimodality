import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart16

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 17 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21347) (q := 21377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21377) (q := 21379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21379) (q := 21383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21383) (q := 21391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21391) (q := 21397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21397) (q := 21401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21401) (q := 21407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21407) (q := 21419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part06_chain :
    DusartPrimeRowsChain 21347 21419 dusartPrimeRows_20959_22026_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21419) (q := 21433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21433) (q := 21467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21467) (q := 21481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21481) (q := 21487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21487) (q := 21491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21491) (q := 21493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21493) (q := 21499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21499) (q := 21503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part07_chain :
    DusartPrimeRowsChain 21419 21503 dusartPrimeRows_20959_22026_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21503) (q := 21517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21517) (q := 21521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21521) (q := 21523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21523) (q := 21529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21529) (q := 21557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21557) (q := 21559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21559) (q := 21563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21563) (q := 21569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part08_chain :
    DusartPrimeRowsChain 21503 21569 dusartPrimeRows_20959_22026_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21569) (q := 21577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21577) (q := 21587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21587) (q := 21589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21589) (q := 21599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21599) (q := 21601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21601) (q := 21611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21611) (q := 21613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21613) (q := 21617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part09_chain :
    DusartPrimeRowsChain 21569 21617 dusartPrimeRows_20959_22026_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21617) (q := 21647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21647) (q := 21649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21649) (q := 21661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21661) (q := 21673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21673) (q := 21683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21683) (q := 21701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21701) (q := 21713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21713) (q := 21727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part10_chain :
    DusartPrimeRowsChain 21617 21727 dusartPrimeRows_20959_22026_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel

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
  decide +kernel
