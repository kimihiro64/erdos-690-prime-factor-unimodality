import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart06

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)

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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num

  exact DusartPrimeRowsChain.empty (by norm_num)
