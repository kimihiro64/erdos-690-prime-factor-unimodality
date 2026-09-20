import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart18

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 19 -/

namespace PrimeFactorUnimodality

noncomputable section
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
