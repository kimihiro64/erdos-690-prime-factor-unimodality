import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 145 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part03_chain :
    DusartPrimeRowsChain 12893 12953 dusartPrimeRows_12713_13366_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 12893 ≤ 12893; omega
  · change 12893 ≤ 12898; omega
  · apply DusartPrimeRowsChain.cons
    · change 12899 ≤ 12899; omega
    · change 12899 ≤ 12906; omega
    · apply DusartPrimeRowsChain.cons
      · change 12907 ≤ 12907; omega
      · change 12907 ≤ 12910; omega
      · apply DusartPrimeRowsChain.cons
        · change 12911 ≤ 12911; omega
        · change 12911 ≤ 12916; omega
        · apply DusartPrimeRowsChain.cons
          · change 12917 ≤ 12917; omega
          · change 12917 ≤ 12918; omega
          · apply DusartPrimeRowsChain.cons
            · change 12919 ≤ 12919; omega
            · change 12919 ≤ 12922; omega
            · apply DusartPrimeRowsChain.cons
              · change 12923 ≤ 12923; omega
              · change 12923 ≤ 12940; omega
              · apply DusartPrimeRowsChain.cons
                · change 12941 ≤ 12941; omega
                · change 12941 ≤ 12952; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
