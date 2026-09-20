import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart26

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 27 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13327 dusartPrimeRows_12713_13366_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13367 dusartPrimeRows_12713_13366_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366 : List DusartPrimeRow :=
  dusartPrimeRows_12713_13366_part01 ++ dusartPrimeRows_12713_13366_part02 ++ dusartPrimeRows_12713_13366_part03 ++ dusartPrimeRows_12713_13366_part04 ++ dusartPrimeRows_12713_13366_part05 ++ dusartPrimeRows_12713_13366_part06 ++ dusartPrimeRows_12713_13366_part07 ++ dusartPrimeRows_12713_13366_part08 ++ dusartPrimeRows_12713_13366_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_chain :
    DusartPrimeRowsChain 12713 13366 dusartPrimeRows_12713_13366 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part08_chain (dusartPrimeRows_12713_13366_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_13366 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12712 ++ dusartPrimeRows_12713_13366

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_13366_chain :
    DusartPrimeRowsChain 3275 13366 dusartPrimeRows_3275_13366 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12712_chain dusartPrimeRows_12713_13366_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part01_chain :
    DusartPrimeRowsChain 13367 13451 dusartPrimeRows_13367_14050_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part02_chain :
    DusartPrimeRowsChain 13451 13523 dusartPrimeRows_13367_14050_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13619 dusartPrimeRows_13367_14050_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
