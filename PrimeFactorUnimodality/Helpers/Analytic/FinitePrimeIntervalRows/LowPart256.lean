import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 256 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19753) (q := 19759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19759) (q := 19763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19763) (q := 19777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19777) (q := 19793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19793) (q := 19801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19801) (q := 19813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19813) (q := 19819) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19819) (q := 19841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part11_chain :
    DusartPrimeRowsChain 19753 19841 dusartPrimeRows_18959_19936_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 19753 ≤ 19753; omega
  · change 19753 ≤ 19758; omega
  · apply DusartPrimeRowsChain.cons
    · change 19759 ≤ 19759; omega
    · change 19759 ≤ 19762; omega
    · apply DusartPrimeRowsChain.cons
      · change 19763 ≤ 19763; omega
      · change 19763 ≤ 19776; omega
      · apply DusartPrimeRowsChain.cons
        · change 19777 ≤ 19777; omega
        · change 19777 ≤ 19792; omega
        · apply DusartPrimeRowsChain.cons
          · change 19793 ≤ 19793; omega
          · change 19793 ≤ 19800; omega
          · apply DusartPrimeRowsChain.cons
            · change 19801 ≤ 19801; omega
            · change 19801 ≤ 19812; omega
            · apply DusartPrimeRowsChain.cons
              · change 19813 ≤ 19813; omega
              · change 19813 ≤ 19818; omega
              · apply DusartPrimeRowsChain.cons
                · change 19819 ≤ 19819; omega
                · change 19819 ≤ 19840; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
