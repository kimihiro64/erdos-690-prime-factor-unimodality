import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 239 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20369) (q := 20389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20389) (q := 20393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20393) (q := 20399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20399) (q := 20407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20407) (q := 20411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20411) (q := 20431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20431) (q := 20441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20441) (q := 20443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part07_chain :
    DusartPrimeRowsChain 20369 20443 dusartPrimeRows_19937_20958_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 20369 ≤ 20369; omega
  · change 20369 ≤ 20388; omega
  · apply DusartPrimeRowsChain.cons
    · change 20389 ≤ 20389; omega
    · change 20389 ≤ 20392; omega
    · apply DusartPrimeRowsChain.cons
      · change 20393 ≤ 20393; omega
      · change 20393 ≤ 20398; omega
      · apply DusartPrimeRowsChain.cons
        · change 20399 ≤ 20399; omega
        · change 20399 ≤ 20406; omega
        · apply DusartPrimeRowsChain.cons
          · change 20407 ≤ 20407; omega
          · change 20407 ≤ 20410; omega
          · apply DusartPrimeRowsChain.cons
            · change 20411 ≤ 20411; omega
            · change 20411 ≤ 20430; omega
            · apply DusartPrimeRowsChain.cons
              · change 20431 ≤ 20431; omega
              · change 20431 ≤ 20440; omega
              · apply DusartPrimeRowsChain.cons
                · change 20441 ≤ 20441; omega
                · change 20441 ≤ 20442; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
