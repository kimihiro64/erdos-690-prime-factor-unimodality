import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 217 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part14_chain :
    DusartPrimeRowsChain 23039 23087 dusartPrimeRows_22027_23158_part14 := by
  apply DusartPrimeRowsChain.cons
  · change 23039 ≤ 23039; omega
  · change 23039 ≤ 23040; omega
  · apply DusartPrimeRowsChain.cons
    · change 23041 ≤ 23041; omega
    · change 23041 ≤ 23052; omega
    · apply DusartPrimeRowsChain.cons
      · change 23053 ≤ 23053; omega
      · change 23053 ≤ 23056; omega
      · apply DusartPrimeRowsChain.cons
        · change 23057 ≤ 23057; omega
        · change 23057 ≤ 23058; omega
        · apply DusartPrimeRowsChain.cons
          · change 23059 ≤ 23059; omega
          · change 23059 ≤ 23062; omega
          · apply DusartPrimeRowsChain.cons
            · change 23063 ≤ 23063; omega
            · change 23063 ≤ 23070; omega
            · apply DusartPrimeRowsChain.cons
              · change 23071 ≤ 23071; omega
              · change 23071 ≤ 23080; omega
              · apply DusartPrimeRowsChain.cons
                · change 23081 ≤ 23081; omega
                · change 23081 ≤ 23086; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
