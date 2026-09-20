import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 92 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part03_chain :
    DusartPrimeRowsChain 9109 9181 dusartPrimeRows_8963_9418_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 9109 ≤ 9109; omega
  · change 9109 ≤ 9126; omega
  · apply DusartPrimeRowsChain.cons
    · change 9127 ≤ 9127; omega
    · change 9127 ≤ 9132; omega
    · apply DusartPrimeRowsChain.cons
      · change 9133 ≤ 9133; omega
      · change 9133 ≤ 9136; omega
      · apply DusartPrimeRowsChain.cons
        · change 9137 ≤ 9137; omega
        · change 9137 ≤ 9150; omega
        · apply DusartPrimeRowsChain.cons
          · change 9151 ≤ 9151; omega
          · change 9151 ≤ 9156; omega
          · apply DusartPrimeRowsChain.cons
            · change 9157 ≤ 9157; omega
            · change 9157 ≤ 9160; omega
            · apply DusartPrimeRowsChain.cons
              · change 9161 ≤ 9161; omega
              · change 9161 ≤ 9172; omega
              · apply DusartPrimeRowsChain.cons
                · change 9173 ≤ 9173; omega
                · change 9173 ≤ 9180; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
