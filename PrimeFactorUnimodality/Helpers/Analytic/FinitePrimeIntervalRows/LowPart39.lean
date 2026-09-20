import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart38

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 39 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7717 dusartPrimeRows_7333_7716_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
