import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart20

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part06_chain :
    DusartPrimeRowsChain 10799 10883 dusartPrimeRows_10427_10938_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10939 dusartPrimeRows_10427_10938_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938 : List DusartPrimeRow :=
  dusartPrimeRows_10427_10938_part01 ++ dusartPrimeRows_10427_10938_part02 ++ dusartPrimeRows_10427_10938_part03 ++ dusartPrimeRows_10427_10938_part04 ++ dusartPrimeRows_10427_10938_part05 ++ dusartPrimeRows_10427_10938_part06 ++ dusartPrimeRows_10427_10938_part07

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_chain :
    DusartPrimeRowsChain 10427 10938 dusartPrimeRows_10427_10938 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_10427_10938_part06_chain (dusartPrimeRows_10427_10938_part07_chain))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_10938 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10426 ++ dusartPrimeRows_10427_10938

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10938_chain :
    DusartPrimeRowsChain 3275 10938 dusartPrimeRows_3275_10938 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10426_chain dusartPrimeRows_10427_10938_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part01_chain :
    DusartPrimeRowsChain 10939 11027 dusartPrimeRows_10939_11502_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part02_chain :
    DusartPrimeRowsChain 11027 11093 dusartPrimeRows_10939_11502_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part03_chain :
    DusartPrimeRowsChain 11093 11171 dusartPrimeRows_10939_11502_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
