import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 01 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part01_chain :
    DusartPrimeRowsChain 3275 3331 dusartPrimeRows_3275_3802_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part02_chain :
    DusartPrimeRowsChain 3331 3391 dusartPrimeRows_3275_3802_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part03_chain :
    DusartPrimeRowsChain 3391 3467 dusartPrimeRows_3275_3802_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part04_chain :
    DusartPrimeRowsChain 3467 3533 dusartPrimeRows_3275_3802_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part05_chain :
    DusartPrimeRowsChain 3533 3583 dusartPrimeRows_3275_3802_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part06_chain :
    DusartPrimeRowsChain 3583 3643 dusartPrimeRows_3275_3802_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part07_chain :
    DusartPrimeRowsChain 3643 3709 dusartPrimeRows_3275_3802_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part08_chain :
    DusartPrimeRowsChain 3709 3779 dusartPrimeRows_3275_3802_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3803 dusartPrimeRows_3275_3802_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802 : List DusartPrimeRow :=
  dusartPrimeRows_3275_3802_part01 ++ dusartPrimeRows_3275_3802_part02 ++ dusartPrimeRows_3275_3802_part03 ++ dusartPrimeRows_3275_3802_part04 ++ dusartPrimeRows_3275_3802_part05 ++ dusartPrimeRows_3275_3802_part06 ++ dusartPrimeRows_3275_3802_part07 ++ dusartPrimeRows_3275_3802_part08 ++ dusartPrimeRows_3275_3802_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_chain :
    DusartPrimeRowsChain 3275 3802 dusartPrimeRows_3275_3802 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_3275_3802_part08_chain (dusartPrimeRows_3275_3802_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part01_chain :
    DusartPrimeRowsChain 3803 3877 dusartPrimeRows_3803_4672_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part02_chain :
    DusartPrimeRowsChain 3877 3929 dusartPrimeRows_3803_4672_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part03_chain :
    DusartPrimeRowsChain 3929 4007 dusartPrimeRows_3803_4672_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4007) (q := 4013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4013) (q := 4019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4019) (q := 4021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4021) (q := 4027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4027) (q := 4049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4049) (q := 4051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4051) (q := 4057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4057) (q := 4073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part04_chain :
    DusartPrimeRowsChain 4007 4073 dusartPrimeRows_3803_4672_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part05_chain :
    DusartPrimeRowsChain 4073 4133 dusartPrimeRows_3803_4672_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4133) (q := 4139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4139) (q := 4153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4153) (q := 4157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4157) (q := 4159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4159) (q := 4177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4177) (q := 4201) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4201) (q := 4211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4211) (q := 4217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part06_chain :
    DusartPrimeRowsChain 4133 4217 dusartPrimeRows_3803_4672_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
