import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart15

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 16 -/

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
