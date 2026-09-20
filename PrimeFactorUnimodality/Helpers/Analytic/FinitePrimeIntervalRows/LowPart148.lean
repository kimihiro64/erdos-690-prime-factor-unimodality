import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 148 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part06_chain :
    DusartPrimeRowsChain 13099 13163 dusartPrimeRows_12713_13366_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 13099 ≤ 13099; omega
  · change 13099 ≤ 13102; omega
  · apply DusartPrimeRowsChain.cons
    · change 13103 ≤ 13103; omega
    · change 13103 ≤ 13108; omega
    · apply DusartPrimeRowsChain.cons
      · change 13109 ≤ 13109; omega
      · change 13109 ≤ 13120; omega
      · apply DusartPrimeRowsChain.cons
        · change 13121 ≤ 13121; omega
        · change 13121 ≤ 13126; omega
        · apply DusartPrimeRowsChain.cons
          · change 13127 ≤ 13127; omega
          · change 13127 ≤ 13146; omega
          · apply DusartPrimeRowsChain.cons
            · change 13147 ≤ 13147; omega
            · change 13147 ≤ 13150; omega
            · apply DusartPrimeRowsChain.cons
              · change 13151 ≤ 13151; omega
              · change 13151 ≤ 13158; omega
              · apply DusartPrimeRowsChain.cons
                · change 13159 ≤ 13159; omega
                · change 13159 ≤ 13162; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
