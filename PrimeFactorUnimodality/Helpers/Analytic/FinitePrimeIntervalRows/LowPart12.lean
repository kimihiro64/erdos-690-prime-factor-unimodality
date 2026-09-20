import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart11

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672 : List DusartPrimeRow :=
  dusartPrimeRows_3803_4672_part01 ++ dusartPrimeRows_3803_4672_part02 ++ dusartPrimeRows_3803_4672_part03 ++ dusartPrimeRows_3803_4672_part04 ++ dusartPrimeRows_3803_4672_part05 ++ dusartPrimeRows_3803_4672_part06 ++ dusartPrimeRows_3803_4672_part07 ++ dusartPrimeRows_3803_4672_part08 ++ dusartPrimeRows_3803_4672_part09 ++ dusartPrimeRows_3803_4672_part10 ++ dusartPrimeRows_3803_4672_part11 ++ dusartPrimeRows_3803_4672_part12 ++ dusartPrimeRows_3803_4672_part13

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_chain :
    DusartPrimeRowsChain 3803 4672 dusartPrimeRows_3803_4672 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part11_chain (dusartPrimeRowsChain_append dusartPrimeRows_3803_4672_part12_chain (dusartPrimeRows_3803_4672_part13_chain))))))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_4672 : List DusartPrimeRow :=
  dusartPrimeRows_3275_3802 ++ dusartPrimeRows_3803_4672

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_4672_chain :
    DusartPrimeRowsChain 3275 4672 dusartPrimeRows_3275_4672 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_3802_chain
    dusartPrimeRows_3803_4672_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part01_chain :
    DusartPrimeRowsChain 4673 4751 dusartPrimeRows_4673_4918_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
