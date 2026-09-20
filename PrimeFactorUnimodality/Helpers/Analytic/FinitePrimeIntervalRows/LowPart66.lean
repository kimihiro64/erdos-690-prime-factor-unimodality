import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 66 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply DusartPrimeRowsChain.cons
  · change 7451 ≤ 7451; omega
  · change 7451 ≤ 7456; omega
  · apply DusartPrimeRowsChain.cons
    · change 7457 ≤ 7457; omega
    · change 7457 ≤ 7458; omega
    · apply DusartPrimeRowsChain.cons
      · change 7459 ≤ 7459; omega
      · change 7459 ≤ 7476; omega
      · apply DusartPrimeRowsChain.cons
        · change 7477 ≤ 7477; omega
        · change 7477 ≤ 7480; omega
        · apply DusartPrimeRowsChain.cons
          · change 7481 ≤ 7481; omega
          · change 7481 ≤ 7486; omega
          · apply DusartPrimeRowsChain.cons
            · change 7487 ≤ 7487; omega
            · change 7487 ≤ 7488; omega
            · apply DusartPrimeRowsChain.cons
              · change 7489 ≤ 7489; omega
              · change 7489 ≤ 7498; omega
              · apply DusartPrimeRowsChain.cons
                · change 7499 ≤ 7499; omega
                · change 7499 ≤ 7506; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
