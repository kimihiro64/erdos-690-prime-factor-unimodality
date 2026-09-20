import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 79 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part03_chain :
    DusartPrimeRowsChain 8263 8317 dusartPrimeRows_8111_8520_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 8263 ≤ 8263; omega
  · change 8263 ≤ 8268; omega
  · apply DusartPrimeRowsChain.cons
    · change 8269 ≤ 8269; omega
    · change 8269 ≤ 8272; omega
    · apply DusartPrimeRowsChain.cons
      · change 8273 ≤ 8273; omega
      · change 8273 ≤ 8286; omega
      · apply DusartPrimeRowsChain.cons
        · change 8287 ≤ 8287; omega
        · change 8287 ≤ 8290; omega
        · apply DusartPrimeRowsChain.cons
          · change 8291 ≤ 8291; omega
          · change 8291 ≤ 8292; omega
          · apply DusartPrimeRowsChain.cons
            · change 8293 ≤ 8293; omega
            · change 8293 ≤ 8296; omega
            · apply DusartPrimeRowsChain.cons
              · change 8297 ≤ 8297; omega
              · change 8297 ≤ 8310; omega
              · apply DusartPrimeRowsChain.cons
                · change 8311 ≤ 8311; omega
                · change 8311 ≤ 8316; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
