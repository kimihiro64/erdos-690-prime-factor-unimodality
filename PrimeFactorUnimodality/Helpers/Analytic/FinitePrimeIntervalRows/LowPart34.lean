import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 34 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part04_chain :
    DusartPrimeRowsChain 5399 5437 dusartPrimeRows_5167_5436_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 5399 ≤ 5399; omega
  · change 5399 ≤ 5406; omega
  · apply DusartPrimeRowsChain.cons
    · change 5407 ≤ 5407; omega
    · change 5407 ≤ 5412; omega
    · apply DusartPrimeRowsChain.cons
      · change 5413 ≤ 5413; omega
      · change 5413 ≤ 5416; omega
      · apply DusartPrimeRowsChain.cons
        · change 5417 ≤ 5417; omega
        · change 5417 ≤ 5418; omega
        · apply DusartPrimeRowsChain.cons
          · change 5419 ≤ 5419; omega
          · change 5419 ≤ 5430; omega
          · apply DusartPrimeRowsChain.cons
            · change 5431 ≤ 5431; omega
            · change 5431 ≤ 5436; omega
            · apply DusartPrimeRowsChain.empty
              norm_num
