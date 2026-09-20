import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart78

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 79 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12713 dusartPrimeRows_12097_12712_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712 : List DusartPrimeRow :=
  dusartPrimeRows_12097_12712_part01 ++ dusartPrimeRows_12097_12712_part02 ++ dusartPrimeRows_12097_12712_part03 ++ dusartPrimeRows_12097_12712_part04 ++ dusartPrimeRows_12097_12712_part05 ++ dusartPrimeRows_12097_12712_part06 ++ dusartPrimeRows_12097_12712_part07 ++ dusartPrimeRows_12097_12712_part08 ++ dusartPrimeRows_12097_12712_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_chain :
    DusartPrimeRowsChain 12097 12712 dusartPrimeRows_12097_12712 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part08_chain (dusartPrimeRows_12097_12712_part09_chain))))))))
