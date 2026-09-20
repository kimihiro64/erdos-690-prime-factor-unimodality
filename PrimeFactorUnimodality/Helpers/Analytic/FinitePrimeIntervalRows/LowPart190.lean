import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 190 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part09_chain :
    DusartPrimeRowsChain 16111 16217 dusartPrimeRows_15527_16318_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 16111 ≤ 16111; omega
  · change 16111 ≤ 16126; omega
  · apply DusartPrimeRowsChain.cons
    · change 16127 ≤ 16127; omega
    · change 16127 ≤ 16138; omega
    · apply DusartPrimeRowsChain.cons
      · change 16139 ≤ 16139; omega
      · change 16139 ≤ 16140; omega
      · apply DusartPrimeRowsChain.cons
        · change 16141 ≤ 16141; omega
        · change 16141 ≤ 16182; omega
        · apply DusartPrimeRowsChain.cons
          · change 16183 ≤ 16183; omega
          · change 16183 ≤ 16186; omega
          · apply DusartPrimeRowsChain.cons
            · change 16187 ≤ 16187; omega
            · change 16187 ≤ 16188; omega
            · apply DusartPrimeRowsChain.cons
              · change 16189 ≤ 16189; omega
              · change 16189 ≤ 16192; omega
              · apply DusartPrimeRowsChain.cons
                · change 16193 ≤ 16193; omega
                · change 16193 ≤ 16216; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
