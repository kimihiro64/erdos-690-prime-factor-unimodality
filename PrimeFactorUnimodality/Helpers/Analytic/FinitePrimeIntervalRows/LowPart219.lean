import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 219 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 20959) (q := 20963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20963) (q := 20981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20981) (q := 20983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20983) (q := 21001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21001) (q := 21011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21011) (q := 21013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21013) (q := 21017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21017) (q := 21019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part01_chain :
    DusartPrimeRowsChain 20959 21019 dusartPrimeRows_20959_22026_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 20959 ≤ 20959; omega
  · change 20959 ≤ 20962; omega
  · apply DusartPrimeRowsChain.cons
    · change 20963 ≤ 20963; omega
    · change 20963 ≤ 20980; omega
    · apply DusartPrimeRowsChain.cons
      · change 20981 ≤ 20981; omega
      · change 20981 ≤ 20982; omega
      · apply DusartPrimeRowsChain.cons
        · change 20983 ≤ 20983; omega
        · change 20983 ≤ 21000; omega
        · apply DusartPrimeRowsChain.cons
          · change 21001 ≤ 21001; omega
          · change 21001 ≤ 21010; omega
          · apply DusartPrimeRowsChain.cons
            · change 21011 ≤ 21011; omega
            · change 21011 ≤ 21012; omega
            · apply DusartPrimeRowsChain.cons
              · change 21013 ≤ 21013; omega
              · change 21013 ≤ 21016; omega
              · apply DusartPrimeRowsChain.cons
                · change 21017 ≤ 21017; omega
                · change 21017 ≤ 21018; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
