import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 232 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21961) (q := 21977) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21977) (q := 21991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21991) (q := 21997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21997) (q := 22003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22003) (q := 22013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22013) (q := 22027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part14_chain :
    DusartPrimeRowsChain 21961 22027 dusartPrimeRows_20959_22026_part14 := by
  apply DusartPrimeRowsChain.cons
  · change 21961 ≤ 21961; omega
  · change 21961 ≤ 21976; omega
  · apply DusartPrimeRowsChain.cons
    · change 21977 ≤ 21977; omega
    · change 21977 ≤ 21990; omega
    · apply DusartPrimeRowsChain.cons
      · change 21991 ≤ 21991; omega
      · change 21991 ≤ 21996; omega
      · apply DusartPrimeRowsChain.cons
        · change 21997 ≤ 21997; omega
        · change 21997 ≤ 22002; omega
        · apply DusartPrimeRowsChain.cons
          · change 22003 ≤ 22003; omega
          · change 22003 ≤ 22012; omega
          · apply DusartPrimeRowsChain.cons
            · change 22013 ≤ 22013; omega
            · change 22013 ≤ 22026; omega
            · apply DusartPrimeRowsChain.empty
              norm_num
