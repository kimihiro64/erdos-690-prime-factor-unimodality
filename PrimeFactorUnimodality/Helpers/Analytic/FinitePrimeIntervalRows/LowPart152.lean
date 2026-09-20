import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 152 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part01_chain :
    DusartPrimeRowsChain 13367 13451 dusartPrimeRows_13367_14050_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 13367 ≤ 13367; omega
  · change 13367 ≤ 13380; omega
  · apply DusartPrimeRowsChain.cons
    · change 13381 ≤ 13381; omega
    · change 13381 ≤ 13396; omega
    · apply DusartPrimeRowsChain.cons
      · change 13397 ≤ 13397; omega
      · change 13397 ≤ 13398; omega
      · apply DusartPrimeRowsChain.cons
        · change 13399 ≤ 13399; omega
        · change 13399 ≤ 13410; omega
        · apply DusartPrimeRowsChain.cons
          · change 13411 ≤ 13411; omega
          · change 13411 ≤ 13416; omega
          · apply DusartPrimeRowsChain.cons
            · change 13417 ≤ 13417; omega
            · change 13417 ≤ 13420; omega
            · apply DusartPrimeRowsChain.cons
              · change 13421 ≤ 13421; omega
              · change 13421 ≤ 13440; omega
              · apply DusartPrimeRowsChain.cons
                · change 13441 ≤ 13441; omega
                · change 13441 ≤ 13450; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
