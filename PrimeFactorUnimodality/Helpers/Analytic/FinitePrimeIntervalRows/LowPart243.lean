import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 243 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20731) (q := 20743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20743) (q := 20747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20747) (q := 20749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20749) (q := 20753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20753) (q := 20759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20759) (q := 20771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20771) (q := 20773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20773) (q := 20789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part11_chain :
    DusartPrimeRowsChain 20731 20789 dusartPrimeRows_19937_20958_part11 := by
  apply DusartPrimeRowsChain.cons
  · change 20731 ≤ 20731; omega
  · change 20731 ≤ 20742; omega
  · apply DusartPrimeRowsChain.cons
    · change 20743 ≤ 20743; omega
    · change 20743 ≤ 20746; omega
    · apply DusartPrimeRowsChain.cons
      · change 20747 ≤ 20747; omega
      · change 20747 ≤ 20748; omega
      · apply DusartPrimeRowsChain.cons
        · change 20749 ≤ 20749; omega
        · change 20749 ≤ 20752; omega
        · apply DusartPrimeRowsChain.cons
          · change 20753 ≤ 20753; omega
          · change 20753 ≤ 20758; omega
          · apply DusartPrimeRowsChain.cons
            · change 20759 ≤ 20759; omega
            · change 20759 ≤ 20770; omega
            · apply DusartPrimeRowsChain.cons
              · change 20771 ≤ 20771; omega
              · change 20771 ≤ 20772; omega
              · apply DusartPrimeRowsChain.cons
                · change 20773 ≤ 20773; omega
                · change 20773 ≤ 20788; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
