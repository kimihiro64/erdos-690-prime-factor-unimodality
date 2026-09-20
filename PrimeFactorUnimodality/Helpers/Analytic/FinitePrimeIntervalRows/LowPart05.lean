import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart04

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 05 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14983 15233 dusartPrimeRows_14767_15526_part02 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 15233 15427 dusartPrimeRows_14767_15526_part03 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part04_chain :
    DusartPrimeRowsChain 15427 15527 dusartPrimeRows_14767_15526_part04 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526 : List DusartPrimeRow :=
  dusartPrimeRows_14767_15526_part01 ++ dusartPrimeRows_14767_15526_part02 ++ dusartPrimeRows_14767_15526_part03 ++ dusartPrimeRows_14767_15526_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_chain :
    DusartPrimeRowsChain 14767 15526 dusartPrimeRows_14767_15526 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_14767_15526_part03_chain (dusartPrimeRows_14767_15526_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_15526 : List DusartPrimeRow :=
  dusartPrimeRows_3275_14766 ++ dusartPrimeRows_14767_15526

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_15526_chain :
    DusartPrimeRowsChain 3275 15526 dusartPrimeRows_3275_15526 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_14766_chain dusartPrimeRows_14767_15526_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part01_chain :
    DusartPrimeRowsChain 15527 15739 dusartPrimeRows_15527_16318_part01 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part02_chain :
    DusartPrimeRowsChain 15739 15971 dusartPrimeRows_15527_16318_part02 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part03_chain :
    DusartPrimeRowsChain 15971 16217 dusartPrimeRows_15527_16318_part03 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),,
    dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part04_chain :
    DusartPrimeRowsChain 16217 16319 dusartPrimeRows_15527_16318_part04 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318 : List DusartPrimeRow :=
  dusartPrimeRows_15527_16318_part01 ++ dusartPrimeRows_15527_16318_part02 ++ dusartPrimeRows_15527_16318_part03 ++ dusartPrimeRows_15527_16318_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_chain :
    DusartPrimeRowsChain 15527 16318 dusartPrimeRows_15527_16318 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_15527_16318_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_15527_16318_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_15527_16318_part03_chain (dusartPrimeRows_15527_16318_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158 : List DusartPrimeRow :=
[
    dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_chain :
    DusartPrimeRowsChain 16319 17158 dusartPrimeRows_16319_17158 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)







set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158 : List DusartPrimeRow :=
[
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_chain :
    DusartPrimeRowsChain 22027 23158 dusartPrimeRows_22027_23158 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)
