import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 179 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part09_chain :
    DusartPrimeRowsChain 15359 15427 dusartPrimeRows_14767_15526_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 15359 ≤ 15359; omega
  · change 15359 ≤ 15360; omega
  · apply DusartPrimeRowsChain.cons
    · change 15361 ≤ 15361; omega
    · change 15361 ≤ 15372; omega
    · apply DusartPrimeRowsChain.cons
      · change 15373 ≤ 15373; omega
      · change 15373 ≤ 15376; omega
      · apply DusartPrimeRowsChain.cons
        · change 15377 ≤ 15377; omega
        · change 15377 ≤ 15382; omega
        · apply DusartPrimeRowsChain.cons
          · change 15383 ≤ 15383; omega
          · change 15383 ≤ 15390; omega
          · apply DusartPrimeRowsChain.cons
            · change 15391 ≤ 15391; omega
            · change 15391 ≤ 15400; omega
            · apply DusartPrimeRowsChain.cons
              · change 15401 ≤ 15401; omega
              · change 15401 ≤ 15412; omega
              · apply DusartPrimeRowsChain.cons
                · change 15413 ≤ 15413; omega
                · change 15413 ≤ 15426; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
