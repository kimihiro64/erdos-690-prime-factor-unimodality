import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart24

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 25 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12517 dusartPrimeRows_12097_12712_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12583 dusartPrimeRows_12097_12712_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12647 dusartPrimeRows_12097_12712_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12713 dusartPrimeRows_12097_12712_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712 : List DusartPrimeRow :=
  dusartPrimeRows_12097_12712_part01 ++ dusartPrimeRows_12097_12712_part02 ++ dusartPrimeRows_12097_12712_part03 ++ dusartPrimeRows_12097_12712_part04 ++ dusartPrimeRows_12097_12712_part05 ++ dusartPrimeRows_12097_12712_part06 ++ dusartPrimeRows_12097_12712_part07 ++ dusartPrimeRows_12097_12712_part08 ++ dusartPrimeRows_12097_12712_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_chain :
    DusartPrimeRowsChain 12097 12712 dusartPrimeRows_12097_12712 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part08_chain (dusartPrimeRows_12097_12712_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_12712 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12096 ++ dusartPrimeRows_12097_12712

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12712_chain :
    DusartPrimeRowsChain 3275 12712 dusartPrimeRows_3275_12712 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12096_chain dusartPrimeRows_12097_12712_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12799 dusartPrimeRows_12713_13366_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
