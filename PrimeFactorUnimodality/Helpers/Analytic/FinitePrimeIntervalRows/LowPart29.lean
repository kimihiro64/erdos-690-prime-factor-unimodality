import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 29 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part03_chain :
    DusartPrimeRowsChain 5021 5099 dusartPrimeRows_4919_5166_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 5021 ≤ 5021; omega
  · change 5021 ≤ 5022; omega
  · apply DusartPrimeRowsChain.cons
    · change 5023 ≤ 5023; omega
    · change 5023 ≤ 5038; omega
    · apply DusartPrimeRowsChain.cons
      · change 5039 ≤ 5039; omega
      · change 5039 ≤ 5050; omega
      · apply DusartPrimeRowsChain.cons
        · change 5051 ≤ 5051; omega
        · change 5051 ≤ 5058; omega
        · apply DusartPrimeRowsChain.cons
          · change 5059 ≤ 5059; omega
          · change 5059 ≤ 5076; omega
          · apply DusartPrimeRowsChain.cons
            · change 5077 ≤ 5077; omega
            · change 5077 ≤ 5080; omega
            · apply DusartPrimeRowsChain.cons
              · change 5081 ≤ 5081; omega
              · change 5081 ≤ 5086; omega
              · apply DusartPrimeRowsChain.cons
                · change 5087 ≤ 5087; omega
                · change 5087 ≤ 5098; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
