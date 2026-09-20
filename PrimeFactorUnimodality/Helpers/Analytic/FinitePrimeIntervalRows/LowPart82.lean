import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart81

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 82 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_8110 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7716 ++ dusartPrimeRows_7717_8110

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8110_chain :
    DusartPrimeRowsChain 3275 8110 dusartPrimeRows_3275_8110 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7716_chain dusartPrimeRows_7717_8110_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part01_chain :
    DusartPrimeRowsChain 8111 8191 dusartPrimeRows_8111_8520_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
