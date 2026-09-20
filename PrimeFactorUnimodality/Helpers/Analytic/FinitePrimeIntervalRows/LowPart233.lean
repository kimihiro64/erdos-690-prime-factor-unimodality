import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 233 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19937) (q := 19949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19949) (q := 19961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19961) (q := 19963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19963) (q := 19973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19973) (q := 19979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19979) (q := 19991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19991) (q := 19993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19993) (q := 19997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part01_chain :
    DusartPrimeRowsChain 19937 19997 dusartPrimeRows_19937_20958_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 19937 ≤ 19937; omega
  · change 19937 ≤ 19948; omega
  · apply DusartPrimeRowsChain.cons
    · change 19949 ≤ 19949; omega
    · change 19949 ≤ 19960; omega
    · apply DusartPrimeRowsChain.cons
      · change 19961 ≤ 19961; omega
      · change 19961 ≤ 19962; omega
      · apply DusartPrimeRowsChain.cons
        · change 19963 ≤ 19963; omega
        · change 19963 ≤ 19972; omega
        · apply DusartPrimeRowsChain.cons
          · change 19973 ≤ 19973; omega
          · change 19973 ≤ 19978; omega
          · apply DusartPrimeRowsChain.cons
            · change 19979 ≤ 19979; omega
            · change 19979 ≤ 19990; omega
            · apply DusartPrimeRowsChain.cons
              · change 19991 ≤ 19991; omega
              · change 19991 ≤ 19992; omega
              · apply DusartPrimeRowsChain.cons
                · change 19993 ≤ 19993; omega
                · change 19993 ≤ 19996; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
