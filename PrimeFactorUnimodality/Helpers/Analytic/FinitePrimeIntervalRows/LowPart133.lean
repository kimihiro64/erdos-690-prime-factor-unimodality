import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart132

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 133 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part08_chain :
    DusartPrimeRowsChain 11489 11503 dusartPrimeRows_10939_11502_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502 : List DusartPrimeRow :=
  dusartPrimeRows_10939_11502_part01 ++ dusartPrimeRows_10939_11502_part02 ++ dusartPrimeRows_10939_11502_part03 ++ dusartPrimeRows_10939_11502_part04 ++ dusartPrimeRows_10939_11502_part05 ++ dusartPrimeRows_10939_11502_part06 ++ dusartPrimeRows_10939_11502_part07 ++ dusartPrimeRows_10939_11502_part08

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_chain :
    DusartPrimeRowsChain 10939 11502 dusartPrimeRows_10939_11502 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part07_chain (dusartPrimeRows_10939_11502_part08_chain)))))))
