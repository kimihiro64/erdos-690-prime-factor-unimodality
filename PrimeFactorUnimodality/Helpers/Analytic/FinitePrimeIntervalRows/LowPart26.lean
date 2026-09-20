import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart25

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 26 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12893 dusartPrimeRows_12713_13366_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part03_chain :
    DusartPrimeRowsChain 12893 12953 dusartPrimeRows_12713_13366_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13007 dusartPrimeRows_12713_13366_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part05_chain :
    DusartPrimeRowsChain 13007 13099 dusartPrimeRows_12713_13366_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part06_chain :
    DusartPrimeRowsChain 13099 13163 dusartPrimeRows_12713_13366_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13241 dusartPrimeRows_12713_13366_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
