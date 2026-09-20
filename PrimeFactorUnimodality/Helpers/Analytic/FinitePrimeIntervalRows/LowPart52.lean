import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart51

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 52 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310 : List DusartPrimeRow :=
  dusartPrimeRows_6007_6310_part01 ++ dusartPrimeRows_6007_6310_part02 ++ dusartPrimeRows_6007_6310_part03 ++ dusartPrimeRows_6007_6310_part04 ++ dusartPrimeRows_6007_6310_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_chain :
    DusartPrimeRowsChain 6007 6310 dusartPrimeRows_6007_6310 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6007_6310_part04_chain (dusartPrimeRows_6007_6310_part05_chain))))
