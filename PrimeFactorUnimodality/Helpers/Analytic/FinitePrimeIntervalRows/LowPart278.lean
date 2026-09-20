import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 278 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17683) (q := 17707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17707) (q := 17713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17713) (q := 17729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17729) (q := 17737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17737) (q := 17747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17747) (q := 17749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17749) (q := 17761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17761) (q := 17783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part08_chain :
    DusartPrimeRowsChain 17683 17783 dusartPrimeRows_17159_18040_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 17683 ≤ 17683; omega
  · change 17683 ≤ 17706; omega
  · apply DusartPrimeRowsChain.cons
    · change 17707 ≤ 17707; omega
    · change 17707 ≤ 17712; omega
    · apply DusartPrimeRowsChain.cons
      · change 17713 ≤ 17713; omega
      · change 17713 ≤ 17728; omega
      · apply DusartPrimeRowsChain.cons
        · change 17729 ≤ 17729; omega
        · change 17729 ≤ 17736; omega
        · apply DusartPrimeRowsChain.cons
          · change 17737 ≤ 17737; omega
          · change 17737 ≤ 17746; omega
          · apply DusartPrimeRowsChain.cons
            · change 17747 ≤ 17747; omega
            · change 17747 ≤ 17748; omega
            · apply DusartPrimeRowsChain.cons
              · change 17749 ≤ 17749; omega
              · change 17749 ≤ 17760; omega
              · apply DusartPrimeRowsChain.cons
                · change 17761 ≤ 17761; omega
                · change 17761 ≤ 17782; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
