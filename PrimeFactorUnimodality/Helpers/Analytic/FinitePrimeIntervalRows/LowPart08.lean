import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart07

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 08 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part02_chain :
    DusartPrimeRowsChain 5791 5849 dusartPrimeRows_5711_6006_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part03_chain :
    DusartPrimeRowsChain 5849 5897 dusartPrimeRows_5711_6006_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part04_chain :
    DusartPrimeRowsChain 5897 6007 dusartPrimeRows_5711_6006_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006 : List DusartPrimeRow :=
  dusartPrimeRows_5711_6006_part01 ++ dusartPrimeRows_5711_6006_part02 ++ dusartPrimeRows_5711_6006_part03 ++ dusartPrimeRows_5711_6006_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_chain :
    DusartPrimeRowsChain 5711 6006 dusartPrimeRows_5711_6006 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_5711_6006_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_5711_6006_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_5711_6006_part03_chain (dusartPrimeRows_5711_6006_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6006 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5710 ++ dusartPrimeRows_5711_6006

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6006_chain :
    DusartPrimeRowsChain 3275 6006 dusartPrimeRows_3275_6006 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5710_chain dusartPrimeRows_5711_6006_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part01_chain :
    DusartPrimeRowsChain 6007 6073 dusartPrimeRows_6007_6310_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part02_chain :
    DusartPrimeRowsChain 6073 6133 dusartPrimeRows_6007_6310_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part03_chain :
    DusartPrimeRowsChain 6133 6211 dusartPrimeRows_6007_6310_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
