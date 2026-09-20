import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 51 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part03_chain :
    DusartPrimeRowsChain 6449 6547 dusartPrimeRows_6311_6636_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 6449 ≤ 6449; omega
  · change 6449 ≤ 6450; omega
  · apply DusartPrimeRowsChain.cons
    · change 6451 ≤ 6451; omega
    · change 6451 ≤ 6468; omega
    · apply DusartPrimeRowsChain.cons
      · change 6469 ≤ 6469; omega
      · change 6469 ≤ 6472; omega
      · apply DusartPrimeRowsChain.cons
        · change 6473 ≤ 6473; omega
        · change 6473 ≤ 6480; omega
        · apply DusartPrimeRowsChain.cons
          · change 6481 ≤ 6481; omega
          · change 6481 ≤ 6490; omega
          · apply DusartPrimeRowsChain.cons
            · change 6491 ≤ 6491; omega
            · change 6491 ≤ 6520; omega
            · apply DusartPrimeRowsChain.cons
              · change 6521 ≤ 6521; omega
              · change 6521 ≤ 6528; omega
              · apply DusartPrimeRowsChain.cons
                · change 6529 ≤ 6529; omega
                · change 6529 ≤ 6546; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
