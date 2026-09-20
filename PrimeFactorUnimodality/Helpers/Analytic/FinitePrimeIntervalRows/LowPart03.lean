import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart02

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_10938 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10426 ++ dusartPrimeRows_10427_10938

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10938_chain :
    DusartPrimeRowsChain 3275 10938 dusartPrimeRows_3275_10938 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10426_chain dusartPrimeRows_10427_10938_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_chain :
    DusartPrimeRowsChain 10939 11502 dusartPrimeRows_10939_11502 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
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
def dusartPrimeRows_3275_11502 : List DusartPrimeRow :=
  dusartPrimeRows_3275_10938 ++ dusartPrimeRows_10939_11502

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_11502_chain :
    DusartPrimeRowsChain 3275 11502 dusartPrimeRows_3275_11502 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_10938_chain dusartPrimeRows_10939_11502_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_chain :
    DusartPrimeRowsChain 11503 12096 dusartPrimeRows_11503_12096 := by
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
def dusartPrimeRows_3275_12096 : List DusartPrimeRow :=
  dusartPrimeRows_3275_11502 ++ dusartPrimeRows_11503_12096

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12096_chain :
    DusartPrimeRowsChain 3275 12096 dusartPrimeRows_3275_12096 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_11502_chain dusartPrimeRows_11503_12096_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_chain :
    DusartPrimeRowsChain 12097 12712 dusartPrimeRows_12097_12712 := by
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
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_12712 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12096 ++ dusartPrimeRows_12097_12712

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_12712_chain :
    DusartPrimeRowsChain 3275 12712 dusartPrimeRows_3275_12712 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12096_chain dusartPrimeRows_12097_12712_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_chain :
    DusartPrimeRowsChain 12713 13366 dusartPrimeRows_12713_13366 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_13366 : List DusartPrimeRow :=
  dusartPrimeRows_3275_12712 ++ dusartPrimeRows_12713_13366

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_13366_chain :
    DusartPrimeRowsChain 3275 13366 dusartPrimeRows_3275_13366 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_12712_chain dusartPrimeRows_12713_13366_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_chain :
    DusartPrimeRowsChain 13367 14050 dusartPrimeRows_13367_14050 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_14050 : List DusartPrimeRow :=
  dusartPrimeRows_3275_13366 ++ dusartPrimeRows_13367_14050

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14050_chain :
    DusartPrimeRowsChain 3275 14050 dusartPrimeRows_3275_14050 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_13366_chain dusartPrimeRows_13367_14050_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_chain :
    DusartPrimeRowsChain 14051 14766 dusartPrimeRows_14051_14766 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_14766 : List DusartPrimeRow :=
  dusartPrimeRows_3275_14050 ++ dusartPrimeRows_14051_14766

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14766_chain :
    DusartPrimeRowsChain 3275 14766 dusartPrimeRows_3275_14766 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_14050_chain dusartPrimeRows_14051_14766_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_chain :
    DusartPrimeRowsChain 14767 15526 dusartPrimeRows_14767_15526 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_15526 : List DusartPrimeRow :=
  dusartPrimeRows_3275_14766 ++ dusartPrimeRows_14767_15526

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_15526_chain :
    DusartPrimeRowsChain 3275 15526 dusartPrimeRows_3275_15526 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_14766_chain dusartPrimeRows_14767_15526_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_chain :
    DusartPrimeRowsChain 15527 16318 dusartPrimeRows_15527_16318 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158 : List DusartPrimeRow :=
[
    dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),

    dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_chain :
    DusartPrimeRowsChain 16319 17158 dusartPrimeRows_16319_17158 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)







set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158 : List DusartPrimeRow :=
[
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_chain :
    DusartPrimeRowsChain 22027 23158 dusartPrimeRows_22027_23158 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)
