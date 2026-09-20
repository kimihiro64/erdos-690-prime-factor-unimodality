import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 67 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  apply DusartPrimeRowsChain.cons
  · change 7507 ≤ 7507; omega
  · change 7507 ≤ 7516; omega
  · apply DusartPrimeRowsChain.cons
    · change 7517 ≤ 7517; omega
    · change 7517 ≤ 7522; omega
    · apply DusartPrimeRowsChain.cons
      · change 7523 ≤ 7523; omega
      · change 7523 ≤ 7528; omega
      · apply DusartPrimeRowsChain.cons
        · change 7529 ≤ 7529; omega
        · change 7529 ≤ 7536; omega
        · apply DusartPrimeRowsChain.cons
          · change 7537 ≤ 7537; omega
          · change 7537 ≤ 7540; omega
          · apply DusartPrimeRowsChain.cons
            · change 7541 ≤ 7541; omega
            · change 7541 ≤ 7546; omega
            · apply DusartPrimeRowsChain.cons
              · change 7547 ≤ 7547; omega
              · change 7547 ≤ 7548; omega
              · apply DusartPrimeRowsChain.cons
                · change 7549 ≤ 7549; omega
                · change 7549 ≤ 7558; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
