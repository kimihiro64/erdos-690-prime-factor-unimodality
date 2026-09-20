import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 168 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part08_chain :
    DusartPrimeRowsChain 14629 14713 dusartPrimeRows_14051_14766_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 14629 ≤ 14629; omega
  · change 14629 ≤ 14632; omega
  · apply DusartPrimeRowsChain.cons
    · change 14633 ≤ 14633; omega
    · change 14633 ≤ 14638; omega
    · apply DusartPrimeRowsChain.cons
      · change 14639 ≤ 14639; omega
      · change 14639 ≤ 14652; omega
      · apply DusartPrimeRowsChain.cons
        · change 14653 ≤ 14653; omega
        · change 14653 ≤ 14656; omega
        · apply DusartPrimeRowsChain.cons
          · change 14657 ≤ 14657; omega
          · change 14657 ≤ 14668; omega
          · apply DusartPrimeRowsChain.cons
            · change 14669 ≤ 14669; omega
            · change 14669 ≤ 14682; omega
            · apply DusartPrimeRowsChain.cons
              · change 14683 ≤ 14683; omega
              · change 14683 ≤ 14698; omega
              · apply DusartPrimeRowsChain.cons
                · change 14699 ≤ 14699; omega
                · change 14699 ≤ 14712; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
