import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart02

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part04_chain :
    DusartPrimeRowsChain 6211 6271 dusartPrimeRows_6007_6310_part04 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part05_chain :
    DusartPrimeRowsChain 6271 6311 dusartPrimeRows_6007_6310_part05 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310 : List DusartPrimeRow :=
  dusartPrimeRows_6007_6310_part01 ++ dusartPrimeRows_6007_6310_part02 ++ dusartPrimeRows_6007_6310_part03 ++ dusartPrimeRows_6007_6310_part04 ++ dusartPrimeRows_6007_6310_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_chain :
    DusartPrimeRowsChain 6007 6310 dusartPrimeRows_6007_6310 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part04_chain (dusartPrimeRows_6007_6310_part05_chain))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6310 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6006 ++ dusartPrimeRows_6007_6310

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6310_chain :
    DusartPrimeRowsChain 3275 6310 dusartPrimeRows_3275_6310 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6006_chain dusartPrimeRows_6007_6310_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part01_chain :
    DusartPrimeRowsChain 6311 6361 dusartPrimeRows_6311_6636_part01 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part02_chain :
    DusartPrimeRowsChain 6361 6449 dusartPrimeRows_6311_6636_part02 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part03_chain :
    DusartPrimeRowsChain 6449 6547 dusartPrimeRows_6311_6636_part03 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part04_chain :
    DusartPrimeRowsChain 6547 6599 dusartPrimeRows_6311_6636_part04 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part05_chain :
    DusartPrimeRowsChain 6599 6637 dusartPrimeRows_6311_6636_part05 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636 : List DusartPrimeRow :=
  dusartPrimeRows_6311_6636_part01 ++ dusartPrimeRows_6311_6636_part02 ++ dusartPrimeRows_6311_6636_part03 ++ dusartPrimeRows_6311_6636_part04 ++ dusartPrimeRows_6311_6636_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_chain :
    DusartPrimeRowsChain 6311 6636 dusartPrimeRows_6311_6636 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6311_6636_part04_chain (dusartPrimeRows_6311_6636_part05_chain))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6636 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6310 ++ dusartPrimeRows_6311_6636

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6636_chain :
    DusartPrimeRowsChain 3275 6636 dusartPrimeRows_3275_6636 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6310_chain dusartPrimeRows_6311_6636_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part01_chain :
    DusartPrimeRowsChain 6637 6701 dusartPrimeRows_6637_6976_part01 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part02_chain :
    DusartPrimeRowsChain 6701 6779 dusartPrimeRows_6637_6976_part02 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part03_chain :
    DusartPrimeRowsChain 6779 6833 dusartPrimeRows_6637_6976_part03 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part04_chain :
    DusartPrimeRowsChain 6833 6907 dusartPrimeRows_6637_6976_part04 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part05_chain :
    DusartPrimeRowsChain 6907 6971 dusartPrimeRows_6637_6976_part05 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part06_chain :
    DusartPrimeRowsChain 6971 6977 dusartPrimeRows_6637_6976_part06 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976 : List DusartPrimeRow :=
  dusartPrimeRows_6637_6976_part01 ++ dusartPrimeRows_6637_6976_part02 ++ dusartPrimeRows_6637_6976_part03 ++ dusartPrimeRows_6637_6976_part04 ++ dusartPrimeRows_6637_6976_part05 ++ dusartPrimeRows_6637_6976_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_chain :
    DusartPrimeRowsChain 6637 6976 dusartPrimeRows_6637_6976 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part05_chain (dusartPrimeRows_6637_6976_part06_chain)))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6976 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6636 ++ dusartPrimeRows_6637_6976

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6976_chain :
    DusartPrimeRowsChain 3275 6976 dusartPrimeRows_3275_6976 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6636_chain dusartPrimeRows_6637_6976_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part01_chain :
    DusartPrimeRowsChain 6977 7039 dusartPrimeRows_6977_7332_part01 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part02_chain :
    DusartPrimeRowsChain 7039 7127 dusartPrimeRows_6977_7332_part02 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)
