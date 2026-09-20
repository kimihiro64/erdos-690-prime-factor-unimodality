import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart03

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 04 -/

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10427_10938_part06]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10427_10938_part07]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part01]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part02]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part04_chain :
    DusartPrimeRowsChain 11171 11257 dusartPrimeRows_10939_11502_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part05_chain :
    DusartPrimeRowsChain 11257 11321 dusartPrimeRows_10939_11502_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part06_chain :
    DusartPrimeRowsChain 11321 11411 dusartPrimeRows_10939_11502_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part07_chain :
    DusartPrimeRowsChain 11411 11489 dusartPrimeRows_10939_11502_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part07]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_10939_11502_part08]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502 : List DusartPrimeRow :=
  dusartPrimeRows_10939_11502_part01 ++ dusartPrimeRows_10939_11502_part02 ++ dusartPrimeRows_10939_11502_part03 ++ dusartPrimeRows_10939_11502_part04 ++ dusartPrimeRows_10939_11502_part05 ++ dusartPrimeRows_10939_11502_part06 ++ dusartPrimeRows_10939_11502_part07 ++ dusartPrimeRows_10939_11502_part08

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_chain :
    DusartPrimeRowsChain 10939 11502 dusartPrimeRows_10939_11502 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_10939_11502_part07_chain (dusartPrimeRows_10939_11502_part08_chain)))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_11502 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10938 ++ dusartPrimeRows_10939_11502

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_11502_chain :
    DusartPrimeRowsChain 3275 11502 dusartPrimeRows_3275_11502 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10938_chain dusartPrimeRows_10939_11502_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part01_chain :
    DusartPrimeRowsChain 11503 11597 dusartPrimeRows_11503_12096_part01 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part01]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part02_chain :
    DusartPrimeRowsChain 11597 11699 dusartPrimeRows_11503_12096_part02 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part02]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part03_chain :
    DusartPrimeRowsChain 11699 11783 dusartPrimeRows_11503_12096_part03 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part04_chain :
    DusartPrimeRowsChain 11783 11833 dusartPrimeRows_11503_12096_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part05_chain :
    DusartPrimeRowsChain 11833 11923 dusartPrimeRows_11503_12096_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part06_chain :
    DusartPrimeRowsChain 11923 11971 dusartPrimeRows_11503_12096_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part07_chain :
    DusartPrimeRowsChain 11971 12049 dusartPrimeRows_11503_12096_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part07]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part08_chain :
    DusartPrimeRowsChain 12049 12097 dusartPrimeRows_11503_12096_part08 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_11503_12096_part08]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096 : List DusartPrimeRow :=
  dusartPrimeRows_11503_12096_part01 ++ dusartPrimeRows_11503_12096_part02 ++ dusartPrimeRows_11503_12096_part03 ++ dusartPrimeRows_11503_12096_part04 ++ dusartPrimeRows_11503_12096_part05 ++ dusartPrimeRows_11503_12096_part06 ++ dusartPrimeRows_11503_12096_part07 ++ dusartPrimeRows_11503_12096_part08

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_chain :
    DusartPrimeRowsChain 11503 12096 dusartPrimeRows_11503_12096 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_11503_12096_part07_chain (dusartPrimeRows_11503_12096_part08_chain)))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_12096 : List DusartPrimeRow :=
  dusartPrimeRows_3275_11502 ++ dusartPrimeRows_11503_12096

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12096_chain :
    DusartPrimeRowsChain 3275 12096 dusartPrimeRows_3275_12096 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_11502_chain dusartPrimeRows_11503_12096_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part01_chain :
    DusartPrimeRowsChain 12097 12157 dusartPrimeRows_12097_12712_part01 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part01]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part02_chain :
    DusartPrimeRowsChain 12157 12241 dusartPrimeRows_12097_12712_part02 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part02]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part03_chain :
    DusartPrimeRowsChain 12241 12301 dusartPrimeRows_12097_12712_part03 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12391 dusartPrimeRows_12097_12712_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12457 dusartPrimeRows_12097_12712_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12517 dusartPrimeRows_12097_12712_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12583 dusartPrimeRows_12097_12712_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part07]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12647 dusartPrimeRows_12097_12712_part08 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part08]

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
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12097_12712_part09]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712 : List DusartPrimeRow :=
  dusartPrimeRows_12097_12712_part01 ++ dusartPrimeRows_12097_12712_part02 ++ dusartPrimeRows_12097_12712_part03 ++ dusartPrimeRows_12097_12712_part04 ++ dusartPrimeRows_12097_12712_part05 ++ dusartPrimeRows_12097_12712_part06 ++ dusartPrimeRows_12097_12712_part07 ++ dusartPrimeRows_12097_12712_part08 ++ dusartPrimeRows_12097_12712_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_chain :
    DusartPrimeRowsChain 12097 12712 dusartPrimeRows_12097_12712 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12097_12712_part08_chain (dusartPrimeRows_12097_12712_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_12712 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12096 ++ dusartPrimeRows_12097_12712

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12712_chain :
    DusartPrimeRowsChain 3275 12712 dusartPrimeRows_3275_12712 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12096_chain dusartPrimeRows_12097_12712_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12799 dusartPrimeRows_12713_13366_part01 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part01]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12893 dusartPrimeRows_12713_13366_part02 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part02]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part03_chain :
    DusartPrimeRowsChain 12893 12953 dusartPrimeRows_12713_13366_part03 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part03]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13007 dusartPrimeRows_12713_13366_part04 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part04]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part05_chain :
    DusartPrimeRowsChain 13007 13099 dusartPrimeRows_12713_13366_part05 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part05]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part06_chain :
    DusartPrimeRowsChain 13099 13163 dusartPrimeRows_12713_13366_part06 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part06]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13241 dusartPrimeRows_12713_13366_part07 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part07]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13327 dusartPrimeRows_12713_13366_part08 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part08]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13367 dusartPrimeRows_12713_13366_part09 := by
  apply dusartPrimeRowsChain_of_data
  norm_num [DusartPrimeRowsChainData, dusartPrimeRows_12713_13366_part09]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366 : List DusartPrimeRow :=
  dusartPrimeRows_12713_13366_part01 ++ dusartPrimeRows_12713_13366_part02 ++ dusartPrimeRows_12713_13366_part03 ++ dusartPrimeRows_12713_13366_part04 ++ dusartPrimeRows_12713_13366_part05 ++ dusartPrimeRows_12713_13366_part06 ++ dusartPrimeRows_12713_13366_part07 ++ dusartPrimeRows_12713_13366_part08 ++ dusartPrimeRows_12713_13366_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_chain :
    DusartPrimeRowsChain 12713 13366 dusartPrimeRows_12713_13366 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_12713_13366_part08_chain (dusartPrimeRows_12713_13366_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_13366 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12712 ++ dusartPrimeRows_12713_13366

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_13366_chain :
    DusartPrimeRowsChain 3275 13366 dusartPrimeRows_3275_13366 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12712_chain dusartPrimeRows_12713_13366_chain
