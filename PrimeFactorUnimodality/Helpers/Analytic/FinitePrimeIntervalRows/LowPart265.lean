import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 265 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18451) (q := 18457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18457) (q := 18461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18461) (q := 18481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18481) (q := 18493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18493) (q := 18503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18503) (q := 18517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18517) (q := 18521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18521) (q := 18523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part07_chain :
    DusartPrimeRowsChain 18451 18523 dusartPrimeRows_18041_18958_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 18451 ≤ 18451; omega
  · change 18451 ≤ 18456; omega
  · apply DusartPrimeRowsChain.cons
    · change 18457 ≤ 18457; omega
    · change 18457 ≤ 18460; omega
    · apply DusartPrimeRowsChain.cons
      · change 18461 ≤ 18461; omega
      · change 18461 ≤ 18480; omega
      · apply DusartPrimeRowsChain.cons
        · change 18481 ≤ 18481; omega
        · change 18481 ≤ 18492; omega
        · apply DusartPrimeRowsChain.cons
          · change 18493 ≤ 18493; omega
          · change 18493 ≤ 18502; omega
          · apply DusartPrimeRowsChain.cons
            · change 18503 ≤ 18503; omega
            · change 18503 ≤ 18516; omega
            · apply DusartPrimeRowsChain.cons
              · change 18517 ≤ 18517; omega
              · change 18517 ≤ 18520; omega
              · apply DusartPrimeRowsChain.cons
                · change 18521 ≤ 18521; omega
                · change 18521 ≤ 18522; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
