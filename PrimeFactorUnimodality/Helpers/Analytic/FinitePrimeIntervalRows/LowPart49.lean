import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart48

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 49 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17599) (q := 17609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17609) (q := 17623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17623) (q := 17627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17627) (q := 17657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17657) (q := 17659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17659) (q := 17669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17669) (q := 17681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17681) (q := 17683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part07_chain :
    DusartPrimeRowsChain 17599 17683 dusartPrimeRows_17159_18040_part07 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17683) (q := 17707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17707) (q := 17713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17713) (q := 17729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17729) (q := 17737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17737) (q := 17747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17747) (q := 17749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17749) (q := 17761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17761) (q := 17783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part08_chain :
    DusartPrimeRowsChain 17683 17783 dusartPrimeRows_17159_18040_part08 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17783) (q := 17789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17789) (q := 17791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17791) (q := 17807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17807) (q := 17827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17827) (q := 17837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17837) (q := 17839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17839) (q := 17851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17851) (q := 17863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part09_chain :
    DusartPrimeRowsChain 17783 17863 dusartPrimeRows_17159_18040_part09 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17863) (q := 17881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17881) (q := 17891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17891) (q := 17903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17903) (q := 17909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17909) (q := 17911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17911) (q := 17921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17921) (q := 17923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17923) (q := 17929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part10_chain :
    DusartPrimeRowsChain 17863 17929 dusartPrimeRows_17159_18040_part10 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17929) (q := 17939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17939) (q := 17957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17957) (q := 17959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17959) (q := 17971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17971) (q := 17977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17977) (q := 17981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17981) (q := 17987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17987) (q := 17989) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part11_chain :
    DusartPrimeRowsChain 17929 17989 dusartPrimeRows_17159_18040_part11 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17989) (q := 18013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 18013) (q := 18041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part12_chain :
    DusartPrimeRowsChain 17989 18041 dusartPrimeRows_17159_18040_part12 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040 : List DusartPrimeRow :=
  dusartPrimeRows_17159_18040_part01 ++ dusartPrimeRows_17159_18040_part02 ++ dusartPrimeRows_17159_18040_part03 ++ dusartPrimeRows_17159_18040_part04 ++ dusartPrimeRows_17159_18040_part05 ++ dusartPrimeRows_17159_18040_part06 ++ dusartPrimeRows_17159_18040_part07 ++ dusartPrimeRows_17159_18040_part08 ++ dusartPrimeRows_17159_18040_part09 ++ dusartPrimeRows_17159_18040_part10 ++ dusartPrimeRows_17159_18040_part11 ++ dusartPrimeRows_17159_18040_part12

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_chain :
    DusartPrimeRowsChain 17159 18040 dusartPrimeRows_17159_18040 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part05_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part06_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part07_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part08_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part09_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part10_chain (dusartPrimeRowsChain_append dusartPrimeRows_17159_18040_part11_chain (dusartPrimeRows_17159_18040_part12_chain)))))))))))
