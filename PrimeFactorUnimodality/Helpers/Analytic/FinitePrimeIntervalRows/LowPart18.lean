import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 18 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part09_chain :
    DusartPrimeRowsChain 4339 4421 dusartPrimeRows_3803_4672_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 4339 ≤ 4339; omega
  · change 4339 ≤ 4348; omega
  · apply DusartPrimeRowsChain.cons
    · change 4349 ≤ 4349; omega
    · change 4349 ≤ 4356; omega
    · apply DusartPrimeRowsChain.cons
      · change 4357 ≤ 4357; omega
      · change 4357 ≤ 4362; omega
      · apply DusartPrimeRowsChain.cons
        · change 4363 ≤ 4363; omega
        · change 4363 ≤ 4372; omega
        · apply DusartPrimeRowsChain.cons
          · change 4373 ≤ 4373; omega
          · change 4373 ≤ 4390; omega
          · apply DusartPrimeRowsChain.cons
            · change 4391 ≤ 4391; omega
            · change 4391 ≤ 4396; omega
            · apply DusartPrimeRowsChain.cons
              · change 4397 ≤ 4397; omega
              · change 4397 ≤ 4408; omega
              · apply DusartPrimeRowsChain.cons
                · change 4409 ≤ 4409; omega
                · change 4409 ≤ 4420; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
