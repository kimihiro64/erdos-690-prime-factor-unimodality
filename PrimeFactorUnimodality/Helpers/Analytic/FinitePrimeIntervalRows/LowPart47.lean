import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 47 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part04_chain :
    DusartPrimeRowsChain 6211 6271 dusartPrimeRows_6007_6310_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 6211 ≤ 6211; omega
  · change 6211 ≤ 6216; omega
  · apply DusartPrimeRowsChain.cons
    · change 6217 ≤ 6217; omega
    · change 6217 ≤ 6220; omega
    · apply DusartPrimeRowsChain.cons
      · change 6221 ≤ 6221; omega
      · change 6221 ≤ 6228; omega
      · apply DusartPrimeRowsChain.cons
        · change 6229 ≤ 6229; omega
        · change 6229 ≤ 6246; omega
        · apply DusartPrimeRowsChain.cons
          · change 6247 ≤ 6247; omega
          · change 6247 ≤ 6256; omega
          · apply DusartPrimeRowsChain.cons
            · change 6257 ≤ 6257; omega
            · change 6257 ≤ 6262; omega
            · apply DusartPrimeRowsChain.cons
              · change 6263 ≤ 6263; omega
              · change 6263 ≤ 6268; omega
              · apply DusartPrimeRowsChain.cons
                · change 6269 ≤ 6269; omega
                · change 6269 ≤ 6270; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
