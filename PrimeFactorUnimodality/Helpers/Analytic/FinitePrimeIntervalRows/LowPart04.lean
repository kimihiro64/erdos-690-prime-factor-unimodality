import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart03

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 04 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part10_chain :
    DusartPrimeRowsChain 4421 4483 dusartPrimeRows_3803_4672_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part11_chain :
    DusartPrimeRowsChain 4483 4549 dusartPrimeRows_3803_4672_part11 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part12_chain :
    DusartPrimeRowsChain 4549 4637 dusartPrimeRows_3803_4672_part12 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part13_chain :
    DusartPrimeRowsChain 4637 4673 dusartPrimeRows_3803_4672_part13 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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
