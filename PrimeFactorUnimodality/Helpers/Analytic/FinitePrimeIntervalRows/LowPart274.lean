import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 274 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17389) (q := 17393) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17393) (q := 17401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17401) (q := 17417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17417) (q := 17419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17419) (q := 17431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17431) (q := 17443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17443) (q := 17449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17449) (q := 17467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part04_chain :
    DusartPrimeRowsChain 17389 17467 dusartPrimeRows_17159_18040_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 17389 ≤ 17389; omega
  · change 17389 ≤ 17392; omega
  · apply DusartPrimeRowsChain.cons
    · change 17393 ≤ 17393; omega
    · change 17393 ≤ 17400; omega
    · apply DusartPrimeRowsChain.cons
      · change 17401 ≤ 17401; omega
      · change 17401 ≤ 17416; omega
      · apply DusartPrimeRowsChain.cons
        · change 17417 ≤ 17417; omega
        · change 17417 ≤ 17418; omega
        · apply DusartPrimeRowsChain.cons
          · change 17419 ≤ 17419; omega
          · change 17419 ≤ 17430; omega
          · apply DusartPrimeRowsChain.cons
            · change 17431 ≤ 17431; omega
            · change 17431 ≤ 17442; omega
            · apply DusartPrimeRowsChain.cons
              · change 17443 ≤ 17443; omega
              · change 17443 ≤ 17448; omega
              · apply DusartPrimeRowsChain.cons
                · change 17449 ≤ 17449; omega
                · change 17449 ≤ 17466; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
