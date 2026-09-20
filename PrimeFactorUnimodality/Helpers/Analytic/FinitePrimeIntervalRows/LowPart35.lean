import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart34

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 35 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part04_chain :
    DusartPrimeRowsChain 16561 16649 dusartPrimeRows_16319_17158_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part05_chain :
    DusartPrimeRowsChain 16649 16703 dusartPrimeRows_16319_17158_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part06_chain :
    DusartPrimeRowsChain 16703 16823 dusartPrimeRows_16319_17158_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part07_chain :
    DusartPrimeRowsChain 16823 16901 dusartPrimeRows_16319_17158_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part08_chain :
    DusartPrimeRowsChain 16901 16979 dusartPrimeRows_16319_17158_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part09_chain :
    DusartPrimeRowsChain 16979 17033 dusartPrimeRows_16319_17158_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
