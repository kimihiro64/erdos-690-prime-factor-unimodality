import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart01

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 02 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_6976 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6636 ++ dusartPrimeRows_6637_6976

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_6976_chain :
    DusartPrimeRowsChain 3275 6976 dusartPrimeRows_3275_6976 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6636_chain dusartPrimeRows_6637_6976_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_chain :
    DusartPrimeRowsChain 6977 7332 dusartPrimeRows_6977_7332 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_7332 : List DusartPrimeRow :=
  dusartPrimeRows_3275_6976 ++ dusartPrimeRows_6977_7332

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7332_chain :
    DusartPrimeRowsChain 3275 7332 dusartPrimeRows_3275_7332 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_6976_chain dusartPrimeRows_6977_7332_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_chain :
    DusartPrimeRowsChain 7333 7716 dusartPrimeRows_7333_7716 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_7716 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7332 ++ dusartPrimeRows_7333_7716

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_7716_chain :
    DusartPrimeRowsChain 3275 7716 dusartPrimeRows_3275_7716 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7332_chain dusartPrimeRows_7333_7716_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_chain :
    DusartPrimeRowsChain 7717 8110 dusartPrimeRows_7717_8110 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_8110 : List DusartPrimeRow :=
  dusartPrimeRows_3275_7716 ++ dusartPrimeRows_7717_8110

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8110_chain :
    DusartPrimeRowsChain 3275 8110 dusartPrimeRows_3275_8110 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_7716_chain dusartPrimeRows_7717_8110_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_chain :
    DusartPrimeRowsChain 8111 8520 dusartPrimeRows_8111_8520 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_8520 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8110 ++ dusartPrimeRows_8111_8520

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8520_chain :
    DusartPrimeRowsChain 3275 8520 dusartPrimeRows_3275_8520 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8110_chain dusartPrimeRows_8111_8520_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_chain :
    DusartPrimeRowsChain 8521 8962 dusartPrimeRows_8521_8962 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_8962 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8520 ++ dusartPrimeRows_8521_8962

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_8962_chain :
    DusartPrimeRowsChain 3275 8962 dusartPrimeRows_3275_8962 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8520_chain dusartPrimeRows_8521_8962_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_chain :
    DusartPrimeRowsChain 8963 9418 dusartPrimeRows_8963_9418 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_9418 : List DusartPrimeRow :=
  dusartPrimeRows_3275_8962 ++ dusartPrimeRows_8963_9418

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_9418_chain :
    DusartPrimeRowsChain 3275 9418 dusartPrimeRows_3275_9418 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_8962_chain dusartPrimeRows_8963_9418_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_chain :
    DusartPrimeRowsChain 9419 9900 dusartPrimeRows_9419_9900 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_9900 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9418 ++ dusartPrimeRows_9419_9900

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_9900_chain :
    DusartPrimeRowsChain 3275 9900 dusartPrimeRows_3275_9900 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9418_chain dusartPrimeRows_9419_9900_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_chain :
    DusartPrimeRowsChain 9901 10426 dusartPrimeRows_9901_10426 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)


set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_10426 : List DusartPrimeRow :=
  dusartPrimeRows_3275_9900 ++ dusartPrimeRows_9901_10426

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_10426_chain :
    DusartPrimeRowsChain 3275 10426 dusartPrimeRows_3275_10426 := by
  exact dusartPrimeRowsChain_append
    dusartPrimeRows_3275_9900_chain dusartPrimeRows_9901_10426_chain

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_chain :
    DusartPrimeRowsChain 10427 10938 dusartPrimeRows_10427_10938 := by
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  apply DusartPrimeRowsChain.cons
    (dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  · norm_num
  · norm_num
  exact DusartPrimeRowsChain.empty (by norm_num)
