import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 257 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19841) (q := 19843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19843) (q := 19853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19853) (q := 19861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19861) (q := 19867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19867) (q := 19889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19889) (q := 19891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19891) (q := 19913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19913) (q := 19919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part12_chain :
    DusartPrimeRowsChain 19841 19919 dusartPrimeRows_18959_19936_part12 := by
  apply DusartPrimeRowsChain.cons
  · change 19841 ≤ 19841; omega
  · change 19841 ≤ 19842; omega
  · apply DusartPrimeRowsChain.cons
    · change 19843 ≤ 19843; omega
    · change 19843 ≤ 19852; omega
    · apply DusartPrimeRowsChain.cons
      · change 19853 ≤ 19853; omega
      · change 19853 ≤ 19860; omega
      · apply DusartPrimeRowsChain.cons
        · change 19861 ≤ 19861; omega
        · change 19861 ≤ 19866; omega
        · apply DusartPrimeRowsChain.cons
          · change 19867 ≤ 19867; omega
          · change 19867 ≤ 19888; omega
          · apply DusartPrimeRowsChain.cons
            · change 19889 ≤ 19889; omega
            · change 19889 ≤ 19890; omega
            · apply DusartPrimeRowsChain.cons
              · change 19891 ≤ 19891; omega
              · change 19891 ≤ 19912; omega
              · apply DusartPrimeRowsChain.cons
                · change 19913 ≤ 19913; omega
                · change 19913 ≤ 19918; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
