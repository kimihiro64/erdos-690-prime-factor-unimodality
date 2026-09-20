import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 235 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20071) (q := 20089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20089) (q := 20101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20101) (q := 20107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20107) (q := 20113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20113) (q := 20117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20117) (q := 20123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20123) (q := 20129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20129) (q := 20143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part03_chain :
    DusartPrimeRowsChain 20071 20143 dusartPrimeRows_19937_20958_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 20071 ≤ 20071; omega
  · change 20071 ≤ 20088; omega
  · apply DusartPrimeRowsChain.cons
    · change 20089 ≤ 20089; omega
    · change 20089 ≤ 20100; omega
    · apply DusartPrimeRowsChain.cons
      · change 20101 ≤ 20101; omega
      · change 20101 ≤ 20106; omega
      · apply DusartPrimeRowsChain.cons
        · change 20107 ≤ 20107; omega
        · change 20107 ≤ 20112; omega
        · apply DusartPrimeRowsChain.cons
          · change 20113 ≤ 20113; omega
          · change 20113 ≤ 20116; omega
          · apply DusartPrimeRowsChain.cons
            · change 20117 ≤ 20117; omega
            · change 20117 ≤ 20122; omega
            · apply DusartPrimeRowsChain.cons
              · change 20123 ≤ 20123; omega
              · change 20123 ≤ 20128; omega
              · apply DusartPrimeRowsChain.cons
                · change 20129 ≤ 20129; omega
                · change 20129 ≤ 20142; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
