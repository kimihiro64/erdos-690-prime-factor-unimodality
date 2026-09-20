import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 31 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part01_chain :
    DusartPrimeRowsChain 5167 5233 dusartPrimeRows_5167_5436_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 5167 ≤ 5167; omega
  · change 5167 ≤ 5170; omega
  · apply DusartPrimeRowsChain.cons
    · change 5171 ≤ 5171; omega
    · change 5171 ≤ 5178; omega
    · apply DusartPrimeRowsChain.cons
      · change 5179 ≤ 5179; omega
      · change 5179 ≤ 5188; omega
      · apply DusartPrimeRowsChain.cons
        · change 5189 ≤ 5189; omega
        · change 5189 ≤ 5196; omega
        · apply DusartPrimeRowsChain.cons
          · change 5197 ≤ 5197; omega
          · change 5197 ≤ 5208; omega
          · apply DusartPrimeRowsChain.cons
            · change 5209 ≤ 5209; omega
            · change 5209 ≤ 5226; omega
            · apply DusartPrimeRowsChain.cons
              · change 5227 ≤ 5227; omega
              · change 5227 ≤ 5230; omega
              · apply DusartPrimeRowsChain.cons
                · change 5231 ≤ 5231; omega
                · change 5231 ≤ 5232; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
