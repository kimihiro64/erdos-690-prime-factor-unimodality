import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 230 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21799) (q := 21803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21803) (q := 21817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21817) (q := 21821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21821) (q := 21839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21839) (q := 21841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21841) (q := 21851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21851) (q := 21859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21859) (q := 21863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part12_chain :
    DusartPrimeRowsChain 21799 21863 dusartPrimeRows_20959_22026_part12 := by
  apply DusartPrimeRowsChain.cons
  · change 21799 ≤ 21799; omega
  · change 21799 ≤ 21802; omega
  · apply DusartPrimeRowsChain.cons
    · change 21803 ≤ 21803; omega
    · change 21803 ≤ 21816; omega
    · apply DusartPrimeRowsChain.cons
      · change 21817 ≤ 21817; omega
      · change 21817 ≤ 21820; omega
      · apply DusartPrimeRowsChain.cons
        · change 21821 ≤ 21821; omega
        · change 21821 ≤ 21838; omega
        · apply DusartPrimeRowsChain.cons
          · change 21839 ≤ 21839; omega
          · change 21839 ≤ 21840; omega
          · apply DusartPrimeRowsChain.cons
            · change 21841 ≤ 21841; omega
            · change 21841 ≤ 21850; omega
            · apply DusartPrimeRowsChain.cons
              · change 21851 ≤ 21851; omega
              · change 21851 ≤ 21858; omega
              · apply DusartPrimeRowsChain.cons
                · change 21859 ≤ 21859; omega
                · change 21859 ≤ 21862; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
