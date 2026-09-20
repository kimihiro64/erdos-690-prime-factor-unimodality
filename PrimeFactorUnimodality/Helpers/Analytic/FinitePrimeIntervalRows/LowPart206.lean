import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 206 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part03_chain :
    DusartPrimeRowsChain 22147 22247 dusartPrimeRows_22027_23158_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 22147 ≤ 22147; omega
  · change 22147 ≤ 22152; omega
  · apply DusartPrimeRowsChain.cons
    · change 22153 ≤ 22153; omega
    · change 22153 ≤ 22156; omega
    · apply DusartPrimeRowsChain.cons
      · change 22157 ≤ 22157; omega
      · change 22157 ≤ 22158; omega
      · apply DusartPrimeRowsChain.cons
        · change 22159 ≤ 22159; omega
        · change 22159 ≤ 22170; omega
        · apply DusartPrimeRowsChain.cons
          · change 22171 ≤ 22171; omega
          · change 22171 ≤ 22188; omega
          · apply DusartPrimeRowsChain.cons
            · change 22189 ≤ 22189; omega
            · change 22189 ≤ 22192; omega
            · apply DusartPrimeRowsChain.cons
              · change 22193 ≤ 22193; omega
              · change 22193 ≤ 22228; omega
              · apply DusartPrimeRowsChain.cons
                · change 22229 ≤ 22229; omega
                · change 22229 ≤ 22246; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
