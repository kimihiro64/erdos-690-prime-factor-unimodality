import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 146 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13007 dusartPrimeRows_12713_13366_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 12953 ≤ 12953; omega
  · change 12953 ≤ 12958; omega
  · apply DusartPrimeRowsChain.cons
    · change 12959 ≤ 12959; omega
    · change 12959 ≤ 12966; omega
    · apply DusartPrimeRowsChain.cons
      · change 12967 ≤ 12967; omega
      · change 12967 ≤ 12972; omega
      · apply DusartPrimeRowsChain.cons
        · change 12973 ≤ 12973; omega
        · change 12973 ≤ 12978; omega
        · apply DusartPrimeRowsChain.cons
          · change 12979 ≤ 12979; omega
          · change 12979 ≤ 12982; omega
          · apply DusartPrimeRowsChain.cons
            · change 12983 ≤ 12983; omega
            · change 12983 ≤ 13000; omega
            · apply DusartPrimeRowsChain.cons
              · change 13001 ≤ 13001; omega
              · change 13001 ≤ 13002; omega
              · apply DusartPrimeRowsChain.cons
                · change 13003 ≤ 13003; omega
                · change 13003 ≤ 13006; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
