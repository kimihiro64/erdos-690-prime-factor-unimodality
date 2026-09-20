import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 40 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part01_chain :
    DusartPrimeRowsChain 5711 5791 dusartPrimeRows_5711_6006_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 5711 ≤ 5711; omega
  · change 5711 ≤ 5716; omega
  · apply DusartPrimeRowsChain.cons
    · change 5717 ≤ 5717; omega
    · change 5717 ≤ 5736; omega
    · apply DusartPrimeRowsChain.cons
      · change 5737 ≤ 5737; omega
      · change 5737 ≤ 5740; omega
      · apply DusartPrimeRowsChain.cons
        · change 5741 ≤ 5741; omega
        · change 5741 ≤ 5742; omega
        · apply DusartPrimeRowsChain.cons
          · change 5743 ≤ 5743; omega
          · change 5743 ≤ 5748; omega
          · apply DusartPrimeRowsChain.cons
            · change 5749 ≤ 5749; omega
            · change 5749 ≤ 5778; omega
            · apply DusartPrimeRowsChain.cons
              · change 5779 ≤ 5779; omega
              · change 5779 ≤ 5782; omega
              · apply DusartPrimeRowsChain.cons
                · change 5783 ≤ 5783; omega
                · change 5783 ≤ 5790; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
