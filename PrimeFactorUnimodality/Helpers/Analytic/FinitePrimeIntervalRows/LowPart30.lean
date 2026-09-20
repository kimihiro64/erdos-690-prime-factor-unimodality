import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 30 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part04_chain :
    DusartPrimeRowsChain 5099 5167 dusartPrimeRows_4919_5166_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 5099 ≤ 5099; omega
  · change 5099 ≤ 5100; omega
  · apply DusartPrimeRowsChain.cons
    · change 5101 ≤ 5101; omega
    · change 5101 ≤ 5106; omega
    · apply DusartPrimeRowsChain.cons
      · change 5107 ≤ 5107; omega
      · change 5107 ≤ 5112; omega
      · apply DusartPrimeRowsChain.cons
        · change 5113 ≤ 5113; omega
        · change 5113 ≤ 5118; omega
        · apply DusartPrimeRowsChain.cons
          · change 5119 ≤ 5119; omega
          · change 5119 ≤ 5146; omega
          · apply DusartPrimeRowsChain.cons
            · change 5147 ≤ 5147; omega
            · change 5147 ≤ 5152; omega
            · apply DusartPrimeRowsChain.cons
              · change 5153 ≤ 5153; omega
              · change 5153 ≤ 5166; omega
              · apply DusartPrimeRowsChain.empty
                norm_num
