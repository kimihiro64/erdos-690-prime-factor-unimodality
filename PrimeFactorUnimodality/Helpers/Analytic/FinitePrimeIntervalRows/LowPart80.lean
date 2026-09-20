import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 80 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part04_chain :
    DusartPrimeRowsChain 8317 8419 dusartPrimeRows_8111_8520_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 8317 ≤ 8317; omega
  · change 8317 ≤ 8328; omega
  · apply DusartPrimeRowsChain.cons
    · change 8329 ≤ 8329; omega
    · change 8329 ≤ 8352; omega
    · apply DusartPrimeRowsChain.cons
      · change 8353 ≤ 8353; omega
      · change 8353 ≤ 8362; omega
      · apply DusartPrimeRowsChain.cons
        · change 8363 ≤ 8363; omega
        · change 8363 ≤ 8368; omega
        · apply DusartPrimeRowsChain.cons
          · change 8369 ≤ 8369; omega
          · change 8369 ≤ 8376; omega
          · apply DusartPrimeRowsChain.cons
            · change 8377 ≤ 8377; omega
            · change 8377 ≤ 8386; omega
            · apply DusartPrimeRowsChain.cons
              · change 8387 ≤ 8387; omega
              · change 8387 ≤ 8388; omega
              · apply DusartPrimeRowsChain.cons
                · change 8389 ≤ 8389; omega
                · change 8389 ≤ 8418; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
