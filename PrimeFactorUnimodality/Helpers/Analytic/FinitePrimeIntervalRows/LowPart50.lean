import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 50 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part02_chain :
    DusartPrimeRowsChain 6361 6449 dusartPrimeRows_6311_6636_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 6361 ≤ 6361; omega
  · change 6361 ≤ 6366; omega
  · apply DusartPrimeRowsChain.cons
    · change 6367 ≤ 6367; omega
    · change 6367 ≤ 6372; omega
    · apply DusartPrimeRowsChain.cons
      · change 6373 ≤ 6373; omega
      · change 6373 ≤ 6378; omega
      · apply DusartPrimeRowsChain.cons
        · change 6379 ≤ 6379; omega
        · change 6379 ≤ 6388; omega
        · apply DusartPrimeRowsChain.cons
          · change 6389 ≤ 6389; omega
          · change 6389 ≤ 6396; omega
          · apply DusartPrimeRowsChain.cons
            · change 6397 ≤ 6397; omega
            · change 6397 ≤ 6420; omega
            · apply DusartPrimeRowsChain.cons
              · change 6421 ≤ 6421; omega
              · change 6421 ≤ 6426; omega
              · apply DusartPrimeRowsChain.cons
                · change 6427 ≤ 6427; omega
                · change 6427 ≤ 6448; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
