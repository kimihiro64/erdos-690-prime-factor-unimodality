import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 65 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply DusartPrimeRowsChain.cons
  · change 7333 ≤ 7333; omega
  · change 7333 ≤ 7348; omega
  · apply DusartPrimeRowsChain.cons
    · change 7349 ≤ 7349; omega
    · change 7349 ≤ 7350; omega
    · apply DusartPrimeRowsChain.cons
      · change 7351 ≤ 7351; omega
      · change 7351 ≤ 7368; omega
      · apply DusartPrimeRowsChain.cons
        · change 7369 ≤ 7369; omega
        · change 7369 ≤ 7392; omega
        · apply DusartPrimeRowsChain.cons
          · change 7393 ≤ 7393; omega
          · change 7393 ≤ 7410; omega
          · apply DusartPrimeRowsChain.cons
            · change 7411 ≤ 7411; omega
            · change 7411 ≤ 7416; omega
            · apply DusartPrimeRowsChain.cons
              · change 7417 ≤ 7417; omega
              · change 7417 ≤ 7432; omega
              · apply DusartPrimeRowsChain.cons
                · change 7433 ≤ 7433; omega
                · change 7433 ≤ 7450; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
