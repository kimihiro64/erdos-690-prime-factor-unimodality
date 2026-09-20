import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart02

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part04_chain :
    DusartPrimeRowsChain 5099 5167 dusartPrimeRows_4919_5166_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166 : List DusartPrimeRow :=
  dusartPrimeRows_4919_5166_part01 ++ dusartPrimeRows_4919_5166_part02 ++ dusartPrimeRows_4919_5166_part03 ++ dusartPrimeRows_4919_5166_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_chain :
    DusartPrimeRowsChain 4919 5166 dusartPrimeRows_4919_5166 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_4919_5166_part03_chain (dusartPrimeRows_4919_5166_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_5166 : List DusartPrimeRow :=
  dusartPrimeRows_3275_4918 ++ dusartPrimeRows_4919_5166

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5166_chain :
    DusartPrimeRowsChain 3275 5166 dusartPrimeRows_3275_5166 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_4918_chain dusartPrimeRows_4919_5166_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part01_chain :
    DusartPrimeRowsChain 5167 5233 dusartPrimeRows_5167_5436_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part02_chain :
    DusartPrimeRowsChain 5233 5309 dusartPrimeRows_5167_5436_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part03_chain :
    DusartPrimeRowsChain 5309 5399 dusartPrimeRows_5167_5436_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part04_chain :
    DusartPrimeRowsChain 5399 5437 dusartPrimeRows_5167_5436_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436 : List DusartPrimeRow :=
  dusartPrimeRows_5167_5436_part01 ++ dusartPrimeRows_5167_5436_part02 ++ dusartPrimeRows_5167_5436_part03 ++ dusartPrimeRows_5167_5436_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_chain :
    DusartPrimeRowsChain 5167 5436 dusartPrimeRows_5167_5436 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_5167_5436_part03_chain (dusartPrimeRows_5167_5436_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_5436 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5166 ++ dusartPrimeRows_5167_5436

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5436_chain :
    DusartPrimeRowsChain 3275 5436 dusartPrimeRows_3275_5436 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5166_chain dusartPrimeRows_5167_5436_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part01_chain :
    DusartPrimeRowsChain 5437 5501 dusartPrimeRows_5437_5710_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part02_chain :
    DusartPrimeRowsChain 5501 5563 dusartPrimeRows_5437_5710_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part03_chain :
    DusartPrimeRowsChain 5563 5647 dusartPrimeRows_5437_5710_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part04_chain :
    DusartPrimeRowsChain 5647 5693 dusartPrimeRows_5437_5710_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part05_chain :
    DusartPrimeRowsChain 5693 5711 dusartPrimeRows_5437_5710_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710 : List DusartPrimeRow :=
  dusartPrimeRows_5437_5710_part01 ++ dusartPrimeRows_5437_5710_part02 ++ dusartPrimeRows_5437_5710_part03 ++ dusartPrimeRows_5437_5710_part04 ++ dusartPrimeRows_5437_5710_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_chain :
    DusartPrimeRowsChain 5437 5710 dusartPrimeRows_5437_5710 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_5437_5710_part04_chain (dusartPrimeRows_5437_5710_part05_chain))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_5710 : List DusartPrimeRow :=
  dusartPrimeRows_3275_5436 ++ dusartPrimeRows_5437_5710

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_5710_chain :
    DusartPrimeRowsChain 3275 5710 dusartPrimeRows_3275_5710 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_5436_chain dusartPrimeRows_5437_5710_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part01_chain :
    DusartPrimeRowsChain 5711 5791 dusartPrimeRows_5711_6006_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
