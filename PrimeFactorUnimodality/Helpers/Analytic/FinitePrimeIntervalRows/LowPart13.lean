import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart12

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 13 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716 : List DusartPrimeRow :=
  dusartPrimeRows_7333_7716_part01 ++ dusartPrimeRows_7333_7716_part02 ++ dusartPrimeRows_7333_7716_part03 ++ dusartPrimeRows_7333_7716_part04 ++ dusartPrimeRows_7333_7716_part05 ++ dusartPrimeRows_7333_7716_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_chain :
    DusartPrimeRowsChain 7333 7716 dusartPrimeRows_7333_7716 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part05_chain (dusartPrimeRows_7333_7716_part06_chain)))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_7716 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7332 ++ dusartPrimeRows_7333_7716

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7716_chain :
    DusartPrimeRowsChain 3275 7716 dusartPrimeRows_3275_7716 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7332_chain dusartPrimeRows_7333_7716_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7793 dusartPrimeRows_7717_8110_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part02_chain :
    DusartPrimeRowsChain 7793 7877 dusartPrimeRows_7717_8110_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part03_chain :
    DusartPrimeRowsChain 7877 7937 dusartPrimeRows_7717_8110_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part04_chain :
    DusartPrimeRowsChain 7937 8039 dusartPrimeRows_7717_8110_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part05_chain :
    DusartPrimeRowsChain 8039 8101 dusartPrimeRows_7717_8110_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
