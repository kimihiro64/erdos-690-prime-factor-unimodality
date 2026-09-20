import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 250 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19301) (q := 19309) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19309) (q := 19319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19319) (q := 19333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19333) (q := 19373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19373) (q := 19379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19379) (q := 19381) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19381) (q := 19387) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19387) (q := 19391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part05_chain :
    DusartPrimeRowsChain 19301 19391 dusartPrimeRows_18959_19936_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 19301 ≤ 19301; omega
  · change 19301 ≤ 19308; omega
  · apply DusartPrimeRowsChain.cons
    · change 19309 ≤ 19309; omega
    · change 19309 ≤ 19318; omega
    · apply DusartPrimeRowsChain.cons
      · change 19319 ≤ 19319; omega
      · change 19319 ≤ 19332; omega
      · apply DusartPrimeRowsChain.cons
        · change 19333 ≤ 19333; omega
        · change 19333 ≤ 19372; omega
        · apply DusartPrimeRowsChain.cons
          · change 19373 ≤ 19373; omega
          · change 19373 ≤ 19378; omega
          · apply DusartPrimeRowsChain.cons
            · change 19379 ≤ 19379; omega
            · change 19379 ≤ 19380; omega
            · apply DusartPrimeRowsChain.cons
              · change 19381 ≤ 19381; omega
              · change 19381 ≤ 19386; omega
              · apply DusartPrimeRowsChain.cons
                · change 19387 ≤ 19387; omega
                · change 19387 ≤ 19390; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
