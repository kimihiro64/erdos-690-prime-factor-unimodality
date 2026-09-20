import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 77 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part01_chain :
    DusartPrimeRowsChain 8111 8191 dusartPrimeRows_8111_8520_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 8111 ≤ 8111; omega
  · change 8111 ≤ 8116; omega
  · apply DusartPrimeRowsChain.cons
    · change 8117 ≤ 8117; omega
    · change 8117 ≤ 8122; omega
    · apply DusartPrimeRowsChain.cons
      · change 8123 ≤ 8123; omega
      · change 8123 ≤ 8146; omega
      · apply DusartPrimeRowsChain.cons
        · change 8147 ≤ 8147; omega
        · change 8147 ≤ 8160; omega
        · apply DusartPrimeRowsChain.cons
          · change 8161 ≤ 8161; omega
          · change 8161 ≤ 8166; omega
          · apply DusartPrimeRowsChain.cons
            · change 8167 ≤ 8167; omega
            · change 8167 ≤ 8170; omega
            · apply DusartPrimeRowsChain.cons
              · change 8171 ≤ 8171; omega
              · change 8171 ≤ 8178; omega
              · apply DusartPrimeRowsChain.cons
                · change 8179 ≤ 8179; omega
                · change 8179 ≤ 8190; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
