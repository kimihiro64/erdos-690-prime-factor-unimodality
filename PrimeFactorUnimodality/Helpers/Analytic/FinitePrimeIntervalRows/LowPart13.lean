import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart12

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 13 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part08_chain :
    DusartPrimeRowsChain 14629 14713 dusartPrimeRows_14051_14766_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part09_chain :
    DusartPrimeRowsChain 14713 14759 dusartPrimeRows_14051_14766_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part10_chain :
    DusartPrimeRowsChain 14759 14767 dusartPrimeRows_14051_14766_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766 : List DusartPrimeRow :=
  dusartPrimeRows_14051_14766_part01 ++ dusartPrimeRows_14051_14766_part02 ++ dusartPrimeRows_14051_14766_part03 ++ dusartPrimeRows_14051_14766_part04 ++ dusartPrimeRows_14051_14766_part05 ++ dusartPrimeRows_14051_14766_part06 ++ dusartPrimeRows_14051_14766_part07 ++ dusartPrimeRows_14051_14766_part08 ++ dusartPrimeRows_14051_14766_part09 ++ dusartPrimeRows_14051_14766_part10

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_chain :
    DusartPrimeRowsChain 14051 14766 dusartPrimeRows_14051_14766 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_14051_14766_part09_chain (dusartPrimeRows_14051_14766_part10_chain)))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_14766 : List DusartPrimeRow :=
  dusartPrimeRows_3275_14050 ++ dusartPrimeRows_14051_14766

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14766_chain :
    DusartPrimeRowsChain 3275 14766 dusartPrimeRows_3275_14766 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_14050_chain dusartPrimeRows_14051_14766_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part01_chain :
    DusartPrimeRowsChain 14767 14831 dusartPrimeRows_14767_15526_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14831 14897 dusartPrimeRows_14767_15526_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 14897 14983 dusartPrimeRows_14767_15526_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part04_chain :
    DusartPrimeRowsChain 14983 15083 dusartPrimeRows_14767_15526_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part05_chain :
    DusartPrimeRowsChain 15083 15149 dusartPrimeRows_14767_15526_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part06_chain :
    DusartPrimeRowsChain 15149 15233 dusartPrimeRows_14767_15526_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part07_chain :
    DusartPrimeRowsChain 15233 15289 dusartPrimeRows_14767_15526_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part08_chain :
    DusartPrimeRowsChain 15289 15359 dusartPrimeRows_14767_15526_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part09_chain :
    DusartPrimeRowsChain 15359 15427 dusartPrimeRows_14767_15526_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part10_chain :
    DusartPrimeRowsChain 15427 15497 dusartPrimeRows_14767_15526_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part11_chain :
    DusartPrimeRowsChain 15497 15527 dusartPrimeRows_14767_15526_part11 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526 : List DusartPrimeRow :=
  dusartPrimeRows_14767_15526_part01 ++ dusartPrimeRows_14767_15526_part02 ++ dusartPrimeRows_14767_15526_part03 ++ dusartPrimeRows_14767_15526_part04 ++ dusartPrimeRows_14767_15526_part05 ++ dusartPrimeRows_14767_15526_part06 ++ dusartPrimeRows_14767_15526_part07 ++ dusartPrimeRows_14767_15526_part08 ++ dusartPrimeRows_14767_15526_part09 ++ dusartPrimeRows_14767_15526_part10 ++ dusartPrimeRows_14767_15526_part11

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_chain :
    DusartPrimeRowsChain 14767 15526 dusartPrimeRows_14767_15526 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part10_chain (dusartPrimeRows_14767_15526_part11_chain))))))))))
