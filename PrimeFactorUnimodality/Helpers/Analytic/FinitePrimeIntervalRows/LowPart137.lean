import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 137 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12391 dusartPrimeRows_12097_12712_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 12301 ≤ 12301; omega
  · change 12301 ≤ 12322; omega
  · apply DusartPrimeRowsChain.cons
    · change 12323 ≤ 12323; omega
    · change 12323 ≤ 12328; omega
    · apply DusartPrimeRowsChain.cons
      · change 12329 ≤ 12329; omega
      · change 12329 ≤ 12342; omega
      · apply DusartPrimeRowsChain.cons
        · change 12343 ≤ 12343; omega
        · change 12343 ≤ 12346; omega
        · apply DusartPrimeRowsChain.cons
          · change 12347 ≤ 12347; omega
          · change 12347 ≤ 12372; omega
          · apply DusartPrimeRowsChain.cons
            · change 12373 ≤ 12373; omega
            · change 12373 ≤ 12376; omega
            · apply DusartPrimeRowsChain.cons
              · change 12377 ≤ 12377; omega
              · change 12377 ≤ 12378; omega
              · apply DusartPrimeRowsChain.cons
                · change 12379 ≤ 12379; omega
                · change 12379 ≤ 12390; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
