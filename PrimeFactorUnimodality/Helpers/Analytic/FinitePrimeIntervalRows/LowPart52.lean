import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 52 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part04_chain :
    DusartPrimeRowsChain 6547 6599 dusartPrimeRows_6311_6636_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 6547 ≤ 6547; omega
  · change 6547 ≤ 6550; omega
  · apply DusartPrimeRowsChain.cons
    · change 6551 ≤ 6551; omega
    · change 6551 ≤ 6552; omega
    · apply DusartPrimeRowsChain.cons
      · change 6553 ≤ 6553; omega
      · change 6553 ≤ 6562; omega
      · apply DusartPrimeRowsChain.cons
        · change 6563 ≤ 6563; omega
        · change 6563 ≤ 6568; omega
        · apply DusartPrimeRowsChain.cons
          · change 6569 ≤ 6569; omega
          · change 6569 ≤ 6570; omega
          · apply DusartPrimeRowsChain.cons
            · change 6571 ≤ 6571; omega
            · change 6571 ≤ 6576; omega
            · apply DusartPrimeRowsChain.cons
              · change 6577 ≤ 6577; omega
              · change 6577 ≤ 6580; omega
              · apply DusartPrimeRowsChain.cons
                · change 6581 ≤ 6581; omega
                · change 6581 ≤ 6598; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
