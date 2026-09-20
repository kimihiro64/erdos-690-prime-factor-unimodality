import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 111 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part01_chain :
    DusartPrimeRowsChain 10427 10487 dusartPrimeRows_10427_10938_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 10427 ≤ 10427; omega
  · change 10427 ≤ 10428; omega
  · apply DusartPrimeRowsChain.cons
    · change 10429 ≤ 10429; omega
    · change 10429 ≤ 10432; omega
    · apply DusartPrimeRowsChain.cons
      · change 10433 ≤ 10433; omega
      · change 10433 ≤ 10452; omega
      · apply DusartPrimeRowsChain.cons
        · change 10453 ≤ 10453; omega
        · change 10453 ≤ 10456; omega
        · apply DusartPrimeRowsChain.cons
          · change 10457 ≤ 10457; omega
          · change 10457 ≤ 10458; omega
          · apply DusartPrimeRowsChain.cons
            · change 10459 ≤ 10459; omega
            · change 10459 ≤ 10462; omega
            · apply DusartPrimeRowsChain.cons
              · change 10463 ≤ 10463; omega
              · change 10463 ≤ 10476; omega
              · apply DusartPrimeRowsChain.cons
                · change 10477 ≤ 10477; omega
                · change 10477 ≤ 10486; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
