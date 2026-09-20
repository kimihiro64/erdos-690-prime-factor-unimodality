import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart04

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 05 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part05_chain :
    DusartPrimeRowsChain 6907 6971 dusartPrimeRows_6637_6976_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332 : List DusartPrimeRow :=
  dusartPrimeRows_6977_7332_part01 ++ dusartPrimeRows_6977_7332_part02 ++ dusartPrimeRows_6977_7332_part03 ++ dusartPrimeRows_6977_7332_part04 ++ dusartPrimeRows_6977_7332_part05

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_chain :
    DusartPrimeRowsChain 6977 7332 dusartPrimeRows_6977_7332 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_6977_7332_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_6977_7332_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_6977_7332_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_6977_7332_part04_chain (dusartPrimeRows_6977_7332_part05_chain))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_7332 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6976 ++ dusartPrimeRows_6977_7332

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7332_chain :
    DusartPrimeRowsChain 3275 7332 dusartPrimeRows_3275_7332 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6976_chain dusartPrimeRows_6977_7332_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part01_chain :
    DusartPrimeRowsChain 7333 7451 dusartPrimeRows_7333_7716_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part02_chain :
    DusartPrimeRowsChain 7451 7507 dusartPrimeRows_7333_7716_part02 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part03_chain :
    DusartPrimeRowsChain 7507 7559 dusartPrimeRows_7333_7716_part03 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part04_chain :
    DusartPrimeRowsChain 7559 7607 dusartPrimeRows_7333_7716_part04 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part05_chain :
    DusartPrimeRowsChain 7607 7687 dusartPrimeRows_7333_7716_part05 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7717 dusartPrimeRows_7333_7716_part06 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716 : List DusartPrimeRow :=
  dusartPrimeRows_7333_7716_part01 ++ dusartPrimeRows_7333_7716_part02 ++ dusartPrimeRows_7333_7716_part03 ++ dusartPrimeRows_7333_7716_part04 ++ dusartPrimeRows_7333_7716_part05 ++ dusartPrimeRows_7333_7716_part06

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_chain :
    DusartPrimeRowsChain 7333 7716 dusartPrimeRows_7333_7716 := by
  exact dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part01_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part02_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part03_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part04_chain (dusartPrimeRowsChain_append dusartPrimeRows_7333_7716_part05_chain (dusartPrimeRows_7333_7716_part06_chain)))))
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_7716 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7332 ++ dusartPrimeRows_7333_7716

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7716_chain :
    DusartPrimeRowsChain 3275 7716 dusartPrimeRows_3275_7716 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7332_chain dusartPrimeRows_7333_7716_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7793 dusartPrimeRows_7717_8110_part01 := by
  apply dusartPrimeRowsChain_of_data
  decide +kernel
