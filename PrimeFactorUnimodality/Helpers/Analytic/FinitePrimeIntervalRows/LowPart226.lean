import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 226 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21503) (q := 21517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21517) (q := 21521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21521) (q := 21523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21523) (q := 21529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21529) (q := 21557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21557) (q := 21559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21559) (q := 21563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21563) (q := 21569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part08_chain :
    DusartPrimeRowsChain 21503 21569 dusartPrimeRows_20959_22026_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 21503 ≤ 21503; omega
  · change 21503 ≤ 21516; omega
  · apply DusartPrimeRowsChain.cons
    · change 21517 ≤ 21517; omega
    · change 21517 ≤ 21520; omega
    · apply DusartPrimeRowsChain.cons
      · change 21521 ≤ 21521; omega
      · change 21521 ≤ 21522; omega
      · apply DusartPrimeRowsChain.cons
        · change 21523 ≤ 21523; omega
        · change 21523 ≤ 21528; omega
        · apply DusartPrimeRowsChain.cons
          · change 21529 ≤ 21529; omega
          · change 21529 ≤ 21556; omega
          · apply DusartPrimeRowsChain.cons
            · change 21557 ≤ 21557; omega
            · change 21557 ≤ 21558; omega
            · apply DusartPrimeRowsChain.cons
              · change 21559 ≤ 21559; omega
              · change 21559 ≤ 21562; omega
              · apply DusartPrimeRowsChain.cons
                · change 21563 ≤ 21563; omega
                · change 21563 ≤ 21568; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
