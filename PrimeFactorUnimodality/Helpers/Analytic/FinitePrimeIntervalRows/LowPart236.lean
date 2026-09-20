import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 236 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20143) (q := 20147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20147) (q := 20149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20149) (q := 20161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20161) (q := 20173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20173) (q := 20177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20177) (q := 20183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20183) (q := 20201) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20201) (q := 20219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part04_chain :
    DusartPrimeRowsChain 20143 20219 dusartPrimeRows_19937_20958_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 20143 ≤ 20143; omega
  · change 20143 ≤ 20146; omega
  · apply DusartPrimeRowsChain.cons
    · change 20147 ≤ 20147; omega
    · change 20147 ≤ 20148; omega
    · apply DusartPrimeRowsChain.cons
      · change 20149 ≤ 20149; omega
      · change 20149 ≤ 20160; omega
      · apply DusartPrimeRowsChain.cons
        · change 20161 ≤ 20161; omega
        · change 20161 ≤ 20172; omega
        · apply DusartPrimeRowsChain.cons
          · change 20173 ≤ 20173; omega
          · change 20173 ≤ 20176; omega
          · apply DusartPrimeRowsChain.cons
            · change 20177 ≤ 20177; omega
            · change 20177 ≤ 20182; omega
            · apply DusartPrimeRowsChain.cons
              · change 20183 ≤ 20183; omega
              · change 20183 ≤ 20200; omega
              · apply DusartPrimeRowsChain.cons
                · change 20201 ≤ 20201; omega
                · change 20201 ≤ 20218; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
