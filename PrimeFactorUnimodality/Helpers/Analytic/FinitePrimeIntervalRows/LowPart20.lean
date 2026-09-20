import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 20 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part11_chain :
    DusartPrimeRowsChain 4483 4549 dusartPrimeRows_3803_4672_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 4483 ≤ 4483; omega
  · change 4483 ≤ 4492; omega
  · apply DusartPrimeRowsChain.cons
    · change 4493 ≤ 4493; omega
    · change 4493 ≤ 4506; omega
    · apply DusartPrimeRowsChain.cons
      · change 4507 ≤ 4507; omega
      · change 4507 ≤ 4512; omega
      · apply DusartPrimeRowsChain.cons
        · change 4513 ≤ 4513; omega
        · change 4513 ≤ 4516; omega
        · apply DusartPrimeRowsChain.cons
          · change 4517 ≤ 4517; omega
          · change 4517 ≤ 4518; omega
          · apply DusartPrimeRowsChain.cons
            · change 4519 ≤ 4519; omega
            · change 4519 ≤ 4522; omega
            · apply DusartPrimeRowsChain.cons
              · change 4523 ≤ 4523; omega
              · change 4523 ≤ 4546; omega
              · apply DusartPrimeRowsChain.cons
                · change 4547 ≤ 4547; omega
                · change 4547 ≤ 4548; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
