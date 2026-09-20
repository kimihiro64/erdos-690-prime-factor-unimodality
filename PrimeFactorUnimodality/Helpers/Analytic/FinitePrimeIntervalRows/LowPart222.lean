import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 222 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21179) (q := 21187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21187) (q := 21191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21191) (q := 21193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21193) (q := 21211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21211) (q := 21221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21221) (q := 21227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21227) (q := 21247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21247) (q := 21269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part04_chain :
    DusartPrimeRowsChain 21179 21269 dusartPrimeRows_20959_22026_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 21179 ≤ 21179; omega
  · change 21179 ≤ 21186; omega
  · apply DusartPrimeRowsChain.cons
    · change 21187 ≤ 21187; omega
    · change 21187 ≤ 21190; omega
    · apply DusartPrimeRowsChain.cons
      · change 21191 ≤ 21191; omega
      · change 21191 ≤ 21192; omega
      · apply DusartPrimeRowsChain.cons
        · change 21193 ≤ 21193; omega
        · change 21193 ≤ 21210; omega
        · apply DusartPrimeRowsChain.cons
          · change 21211 ≤ 21211; omega
          · change 21211 ≤ 21220; omega
          · apply DusartPrimeRowsChain.cons
            · change 21221 ≤ 21221; omega
            · change 21221 ≤ 21226; omega
            · apply DusartPrimeRowsChain.cons
              · change 21227 ≤ 21227; omega
              · change 21227 ≤ 21246; omega
              · apply DusartPrimeRowsChain.cons
                · change 21247 ≤ 21247; omega
                · change 21247 ≤ 21268; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
