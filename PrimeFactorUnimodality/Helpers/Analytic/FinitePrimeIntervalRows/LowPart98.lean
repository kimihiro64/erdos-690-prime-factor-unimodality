import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 98 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part02_chain :
    DusartPrimeRowsChain 9467 9539 dusartPrimeRows_9419_9900_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 9467 ≤ 9467; omega
  · change 9467 ≤ 9472; omega
  · apply DusartPrimeRowsChain.cons
    · change 9473 ≤ 9473; omega
    · change 9473 ≤ 9478; omega
    · apply DusartPrimeRowsChain.cons
      · change 9479 ≤ 9479; omega
      · change 9479 ≤ 9490; omega
      · apply DusartPrimeRowsChain.cons
        · change 9491 ≤ 9491; omega
        · change 9491 ≤ 9496; omega
        · apply DusartPrimeRowsChain.cons
          · change 9497 ≤ 9497; omega
          · change 9497 ≤ 9510; omega
          · apply DusartPrimeRowsChain.cons
            · change 9511 ≤ 9511; omega
            · change 9511 ≤ 9520; omega
            · apply DusartPrimeRowsChain.cons
              · change 9521 ≤ 9521; omega
              · change 9521 ≤ 9532; omega
              · apply DusartPrimeRowsChain.cons
                · change 9533 ≤ 9533; omega
                · change 9533 ≤ 9538; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
