import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart05

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 06 -/

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
