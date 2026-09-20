import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 157 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part06_chain :
    DusartPrimeRowsChain 13751 13829 dusartPrimeRows_13367_14050_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 13751 ≤ 13751; omega
  · change 13751 ≤ 13756; omega
  · apply DusartPrimeRowsChain.cons
    · change 13757 ≤ 13757; omega
    · change 13757 ≤ 13758; omega
    · apply DusartPrimeRowsChain.cons
      · change 13759 ≤ 13759; omega
      · change 13759 ≤ 13762; omega
      · apply DusartPrimeRowsChain.cons
        · change 13763 ≤ 13763; omega
        · change 13763 ≤ 13780; omega
        · apply DusartPrimeRowsChain.cons
          · change 13781 ≤ 13781; omega
          · change 13781 ≤ 13788; omega
          · apply DusartPrimeRowsChain.cons
            · change 13789 ≤ 13789; omega
            · change 13789 ≤ 13798; omega
            · apply DusartPrimeRowsChain.cons
              · change 13799 ≤ 13799; omega
              · change 13799 ≤ 13806; omega
              · apply DusartPrimeRowsChain.cons
                · change 13807 ≤ 13807; omega
                · change 13807 ≤ 13828; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
