import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart20

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
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
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_16318 : List DusartPrimeRow :=
  dusartPrimeRows_3275_15526 ++ dusartPrimeRows_15527_16318

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_16318_chain :
    DusartPrimeRowsChain 3275 16318 dusartPrimeRows_3275_16318 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_15526_chain dusartPrimeRows_15527_16318_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_17158 : List DusartPrimeRow :=
  dusartPrimeRows_3275_16318 ++ dusartPrimeRows_16319_17158

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_17158_chain :
    DusartPrimeRowsChain 3275 17158 dusartPrimeRows_3275_17158 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_16318_chain dusartPrimeRows_16319_17158_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_18040 : List DusartPrimeRow :=
  dusartPrimeRows_3275_17158 ++ dusartPrimeRows_17159_18040

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_18040_chain :
    DusartPrimeRowsChain 3275 18040 dusartPrimeRows_3275_18040 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_17158_chain dusartPrimeRows_17159_18040_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_18958 : List DusartPrimeRow :=
  dusartPrimeRows_3275_18040 ++ dusartPrimeRows_18041_18958

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_18958_chain :
    DusartPrimeRowsChain 3275 18958 dusartPrimeRows_3275_18958 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_18040_chain dusartPrimeRows_18041_18958_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_19936 : List DusartPrimeRow :=
  dusartPrimeRows_3275_18958 ++ dusartPrimeRows_18959_19936

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_19936_chain :
    DusartPrimeRowsChain 3275 19936 dusartPrimeRows_3275_19936 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_18958_chain dusartPrimeRows_18959_19936_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_20958 : List DusartPrimeRow :=
  dusartPrimeRows_3275_19936 ++ dusartPrimeRows_19937_20958

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_20958_chain :
    DusartPrimeRowsChain 3275 20958 dusartPrimeRows_3275_20958 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_19936_chain dusartPrimeRows_19937_20958_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_22026 : List DusartPrimeRow :=
  dusartPrimeRows_3275_20958 ++ dusartPrimeRows_20959_22026

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_22026_chain :
    DusartPrimeRowsChain 3275 22026 dusartPrimeRows_3275_22026 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_20958_chain dusartPrimeRows_20959_22026_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_23158 : List DusartPrimeRow :=
  dusartPrimeRows_3275_22026 ++ dusartPrimeRows_22027_23158

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_23158_chain :
    DusartPrimeRowsChain 3275 23158 dusartPrimeRows_3275_23158 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_22026_chain dusartPrimeRows_22027_23158_chain
