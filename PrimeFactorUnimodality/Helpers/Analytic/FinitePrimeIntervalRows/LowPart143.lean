import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 143 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12799 dusartPrimeRows_12713_13366_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 12713 ≤ 12713; omega
  · change 12713 ≤ 12720; omega
  · apply DusartPrimeRowsChain.cons
    · change 12721 ≤ 12721; omega
    · change 12721 ≤ 12738; omega
    · apply DusartPrimeRowsChain.cons
      · change 12739 ≤ 12739; omega
      · change 12739 ≤ 12742; omega
      · apply DusartPrimeRowsChain.cons
        · change 12743 ≤ 12743; omega
        · change 12743 ≤ 12756; omega
        · apply DusartPrimeRowsChain.cons
          · change 12757 ≤ 12757; omega
          · change 12757 ≤ 12762; omega
          · apply DusartPrimeRowsChain.cons
            · change 12763 ≤ 12763; omega
            · change 12763 ≤ 12780; omega
            · apply DusartPrimeRowsChain.cons
              · change 12781 ≤ 12781; omega
              · change 12781 ≤ 12790; omega
              · apply DusartPrimeRowsChain.cons
                · change 12791 ≤ 12791; omega
                · change 12791 ≤ 12798; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
