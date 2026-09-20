import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 147 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part05_chain :
    DusartPrimeRowsChain 13007 13099 dusartPrimeRows_12713_13366_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 13007 ≤ 13007; omega
  · change 13007 ≤ 13008; omega
  · apply DusartPrimeRowsChain.cons
    · change 13009 ≤ 13009; omega
    · change 13009 ≤ 13032; omega
    · apply DusartPrimeRowsChain.cons
      · change 13033 ≤ 13033; omega
      · change 13033 ≤ 13036; omega
      · apply DusartPrimeRowsChain.cons
        · change 13037 ≤ 13037; omega
        · change 13037 ≤ 13042; omega
        · apply DusartPrimeRowsChain.cons
          · change 13043 ≤ 13043; omega
          · change 13043 ≤ 13048; omega
          · apply DusartPrimeRowsChain.cons
            · change 13049 ≤ 13049; omega
            · change 13049 ≤ 13062; omega
            · apply DusartPrimeRowsChain.cons
              · change 13063 ≤ 13063; omega
              · change 13063 ≤ 13092; omega
              · apply DusartPrimeRowsChain.cons
                · change 13093 ≤ 13093; omega
                · change 13093 ≤ 13098; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
