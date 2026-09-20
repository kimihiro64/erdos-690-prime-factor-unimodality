import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 112 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part02_chain :
    DusartPrimeRowsChain 10487 10589 dusartPrimeRows_10427_10938_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 10487 ≤ 10487; omega
  · change 10487 ≤ 10498; omega
  · apply DusartPrimeRowsChain.cons
    · change 10499 ≤ 10499; omega
    · change 10499 ≤ 10500; omega
    · apply DusartPrimeRowsChain.cons
      · change 10501 ≤ 10501; omega
      · change 10501 ≤ 10512; omega
      · apply DusartPrimeRowsChain.cons
        · change 10513 ≤ 10513; omega
        · change 10513 ≤ 10528; omega
        · apply DusartPrimeRowsChain.cons
          · change 10529 ≤ 10529; omega
          · change 10529 ≤ 10530; omega
          · apply DusartPrimeRowsChain.cons
            · change 10531 ≤ 10531; omega
            · change 10531 ≤ 10558; omega
            · apply DusartPrimeRowsChain.cons
              · change 10559 ≤ 10559; omega
              · change 10559 ≤ 10566; omega
              · apply DusartPrimeRowsChain.cons
                · change 10567 ≤ 10567; omega
                · change 10567 ≤ 10588; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
