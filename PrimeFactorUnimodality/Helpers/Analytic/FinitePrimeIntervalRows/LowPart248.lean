import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 248 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19141) (q := 19157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19157) (q := 19163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19163) (q := 19181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19181) (q := 19183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19183) (q := 19207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19207) (q := 19211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19211) (q := 19213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19213) (q := 19219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part03_chain :
    DusartPrimeRowsChain 19141 19219 dusartPrimeRows_18959_19936_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 19141 ≤ 19141; omega
  · change 19141 ≤ 19156; omega
  · apply DusartPrimeRowsChain.cons
    · change 19157 ≤ 19157; omega
    · change 19157 ≤ 19162; omega
    · apply DusartPrimeRowsChain.cons
      · change 19163 ≤ 19163; omega
      · change 19163 ≤ 19180; omega
      · apply DusartPrimeRowsChain.cons
        · change 19181 ≤ 19181; omega
        · change 19181 ≤ 19182; omega
        · apply DusartPrimeRowsChain.cons
          · change 19183 ≤ 19183; omega
          · change 19183 ≤ 19206; omega
          · apply DusartPrimeRowsChain.cons
            · change 19207 ≤ 19207; omega
            · change 19207 ≤ 19210; omega
            · apply DusartPrimeRowsChain.cons
              · change 19211 ≤ 19211; omega
              · change 19211 ≤ 19212; omega
              · apply DusartPrimeRowsChain.cons
                · change 19213 ≤ 19213; omega
                · change 19213 ≤ 19218; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
