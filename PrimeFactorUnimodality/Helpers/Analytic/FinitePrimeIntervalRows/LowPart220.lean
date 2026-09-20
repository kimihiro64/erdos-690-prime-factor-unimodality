import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 220 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21019) (q := 21023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21023) (q := 21031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21031) (q := 21059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21059) (q := 21061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21061) (q := 21067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21067) (q := 21089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21089) (q := 21101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21101) (q := 21107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part02_chain :
    DusartPrimeRowsChain 21019 21107 dusartPrimeRows_20959_22026_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 21019 ≤ 21019; omega
  · change 21019 ≤ 21022; omega
  · apply DusartPrimeRowsChain.cons
    · change 21023 ≤ 21023; omega
    · change 21023 ≤ 21030; omega
    · apply DusartPrimeRowsChain.cons
      · change 21031 ≤ 21031; omega
      · change 21031 ≤ 21058; omega
      · apply DusartPrimeRowsChain.cons
        · change 21059 ≤ 21059; omega
        · change 21059 ≤ 21060; omega
        · apply DusartPrimeRowsChain.cons
          · change 21061 ≤ 21061; omega
          · change 21061 ≤ 21066; omega
          · apply DusartPrimeRowsChain.cons
            · change 21067 ≤ 21067; omega
            · change 21067 ≤ 21088; omega
            · apply DusartPrimeRowsChain.cons
              · change 21089 ≤ 21089; omega
              · change 21089 ≤ 21100; omega
              · apply DusartPrimeRowsChain.cons
                · change 21101 ≤ 21101; omega
                · change 21101 ≤ 21106; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
