import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 78 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part02_chain :
    DusartPrimeRowsChain 8191 8263 dusartPrimeRows_8111_8520_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 8191 ≤ 8191; omega
  · change 8191 ≤ 8208; omega
  · apply DusartPrimeRowsChain.cons
    · change 8209 ≤ 8209; omega
    · change 8209 ≤ 8218; omega
    · apply DusartPrimeRowsChain.cons
      · change 8219 ≤ 8219; omega
      · change 8219 ≤ 8220; omega
      · apply DusartPrimeRowsChain.cons
        · change 8221 ≤ 8221; omega
        · change 8221 ≤ 8230; omega
        · apply DusartPrimeRowsChain.cons
          · change 8231 ≤ 8231; omega
          · change 8231 ≤ 8232; omega
          · apply DusartPrimeRowsChain.cons
            · change 8233 ≤ 8233; omega
            · change 8233 ≤ 8236; omega
            · apply DusartPrimeRowsChain.cons
              · change 8237 ≤ 8237; omega
              · change 8237 ≤ 8242; omega
              · apply DusartPrimeRowsChain.cons
                · change 8243 ≤ 8243; omega
                · change 8243 ≤ 8262; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
