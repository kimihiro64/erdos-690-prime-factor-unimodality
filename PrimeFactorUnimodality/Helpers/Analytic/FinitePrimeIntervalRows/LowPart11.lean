import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart10

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 11 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part06_chain :
    DusartPrimeRowsChain 6971 6977 dusartPrimeRows_6637_6976_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976 : List DusartPrimeRow :=
  dusartPrimeRows_6637_6976_part01 ++ dusartPrimeRows_6637_6976_part02 ++ dusartPrimeRows_6637_6976_part03 ++ dusartPrimeRows_6637_6976_part04 ++ dusartPrimeRows_6637_6976_part05 ++ dusartPrimeRows_6637_6976_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_chain :
    DusartPrimeRowsChain 6637 6976 dusartPrimeRows_6637_6976 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_6637_6976_part05_chain (dusartPrimeRows_6637_6976_part06_chain)))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6976 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6636 ++ dusartPrimeRows_6637_6976

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6976_chain :
    DusartPrimeRowsChain 3275 6976 dusartPrimeRows_3275_6976 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6636_chain dusartPrimeRows_6637_6976_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part01_chain :
    DusartPrimeRowsChain 6977 7039 dusartPrimeRows_6977_7332_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part02_chain :
    DusartPrimeRowsChain 7039 7127 dusartPrimeRows_6977_7332_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part03_chain :
    DusartPrimeRowsChain 7127 7211 dusartPrimeRows_6977_7332_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part04_chain :
    DusartPrimeRowsChain 7211 7283 dusartPrimeRows_6977_7332_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part05_chain :
    DusartPrimeRowsChain 7283 7333 dusartPrimeRows_6977_7332_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
