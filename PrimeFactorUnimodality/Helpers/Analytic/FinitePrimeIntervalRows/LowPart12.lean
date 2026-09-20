import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart11

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13619 dusartPrimeRows_13367_14050_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part04_chain :
    DusartPrimeRowsChain 13619 13691 dusartPrimeRows_13367_14050_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part05_chain :
    DusartPrimeRowsChain 13691 13751 dusartPrimeRows_13367_14050_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part06_chain :
    DusartPrimeRowsChain 13751 13829 dusartPrimeRows_13367_14050_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part07_chain :
    DusartPrimeRowsChain 13829 13901 dusartPrimeRows_13367_14050_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part08_chain :
    DusartPrimeRowsChain 13901 13967 dusartPrimeRows_13367_14050_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part09_chain :
    DusartPrimeRowsChain 13967 14051 dusartPrimeRows_13367_14050_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050 : List DusartPrimeRow :=
  dusartPrimeRows_13367_14050_part01 ++ dusartPrimeRows_13367_14050_part02 ++ dusartPrimeRows_13367_14050_part03 ++ dusartPrimeRows_13367_14050_part04 ++ dusartPrimeRows_13367_14050_part05 ++ dusartPrimeRows_13367_14050_part06 ++ dusartPrimeRows_13367_14050_part07 ++ dusartPrimeRows_13367_14050_part08 ++ dusartPrimeRows_13367_14050_part09

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_chain :
    DusartPrimeRowsChain 13367 14050 dusartPrimeRows_13367_14050 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_13367_14050_part08_chain (dusartPrimeRows_13367_14050_part09_chain))))))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_14050 : List DusartPrimeRow :=
  dusartPrimeRows_3275_13366 ++ dusartPrimeRows_13367_14050

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_14050_chain :
    DusartPrimeRowsChain 3275 14050 dusartPrimeRows_3275_14050 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_13366_chain dusartPrimeRows_13367_14050_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part01_chain :
    DusartPrimeRowsChain 14051 14149 dusartPrimeRows_14051_14766_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part02_chain :
    DusartPrimeRowsChain 14149 14243 dusartPrimeRows_14051_14766_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part03_chain :
    DusartPrimeRowsChain 14243 14327 dusartPrimeRows_14051_14766_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part04_chain :
    DusartPrimeRowsChain 14327 14411 dusartPrimeRows_14051_14766_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part05_chain :
    DusartPrimeRowsChain 14411 14479 dusartPrimeRows_14051_14766_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part06_chain :
    DusartPrimeRowsChain 14479 14551 dusartPrimeRows_14051_14766_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part07_chain :
    DusartPrimeRowsChain 14551 14629 dusartPrimeRows_14051_14766_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
