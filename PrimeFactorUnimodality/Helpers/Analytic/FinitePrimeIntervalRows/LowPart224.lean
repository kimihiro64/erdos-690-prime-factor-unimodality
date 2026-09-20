import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 224 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21347) (q := 21377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21377) (q := 21379) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21379) (q := 21383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21383) (q := 21391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21391) (q := 21397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21397) (q := 21401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21401) (q := 21407) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21407) (q := 21419) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part06_chain :
    DusartPrimeRowsChain 21347 21419 dusartPrimeRows_20959_22026_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 21347 ≤ 21347; omega
  · change 21347 ≤ 21376; omega
  · apply DusartPrimeRowsChain.cons
    · change 21377 ≤ 21377; omega
    · change 21377 ≤ 21378; omega
    · apply DusartPrimeRowsChain.cons
      · change 21379 ≤ 21379; omega
      · change 21379 ≤ 21382; omega
      · apply DusartPrimeRowsChain.cons
        · change 21383 ≤ 21383; omega
        · change 21383 ≤ 21390; omega
        · apply DusartPrimeRowsChain.cons
          · change 21391 ≤ 21391; omega
          · change 21391 ≤ 21396; omega
          · apply DusartPrimeRowsChain.cons
            · change 21397 ≤ 21397; omega
            · change 21397 ≤ 21400; omega
            · apply DusartPrimeRowsChain.cons
              · change 21401 ≤ 21401; omega
              · change 21401 ≤ 21406; omega
              · apply DusartPrimeRowsChain.cons
                · change 21407 ≤ 21407; omega
                · change 21407 ≤ 21418; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
