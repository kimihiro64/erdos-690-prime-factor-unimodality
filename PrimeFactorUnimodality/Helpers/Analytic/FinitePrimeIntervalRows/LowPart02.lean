import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart01

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 02 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part07_chain :
    DusartPrimeRowsChain 4217 4261 dusartPrimeRows_3803_4672_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part08_chain :
    DusartPrimeRowsChain 4261 4339 dusartPrimeRows_3803_4672_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part09_chain :
    DusartPrimeRowsChain 4339 4421 dusartPrimeRows_3803_4672_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part02_chain :
    DusartPrimeRowsChain 4751 4813 dusartPrimeRows_4673_4918_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part03_chain :
    DusartPrimeRowsChain 4813 4909 dusartPrimeRows_4673_4918_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part04_chain :
    DusartPrimeRowsChain 4909 4919 dusartPrimeRows_4673_4918_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918 : List DusartPrimeRow :=
  dusartPrimeRows_4673_4918_part01 ++ dusartPrimeRows_4673_4918_part02 ++ dusartPrimeRows_4673_4918_part03 ++ dusartPrimeRows_4673_4918_part04

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_chain :
    DusartPrimeRowsChain 4673 4918 dusartPrimeRows_4673_4918 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_4673_4918_part03_chain (dusartPrimeRows_4673_4918_part04_chain)))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_4918 : List DusartPrimeRow :=
  dusartPrimeRows_3275_4672 ++ dusartPrimeRows_4673_4918

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_4918_chain :
    DusartPrimeRowsChain 3275 4918 dusartPrimeRows_3275_4918 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_4672_chain dusartPrimeRows_4673_4918_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part01_chain :
    DusartPrimeRowsChain 4919 4969 dusartPrimeRows_4919_5166_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part02_chain :
    DusartPrimeRowsChain 4969 5021 dusartPrimeRows_4919_5166_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part03_chain :
    DusartPrimeRowsChain 5021 5099 dusartPrimeRows_4919_5166_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
