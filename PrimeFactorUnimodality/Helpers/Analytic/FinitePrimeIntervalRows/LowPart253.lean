import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 253 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19489) (q := 19501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19501) (q := 19507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19507) (q := 19531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19531) (q := 19541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19541) (q := 19543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19543) (q := 19553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19553) (q := 19559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19559) (q := 19571) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part08_chain :
    DusartPrimeRowsChain 19489 19571 dusartPrimeRows_18959_19936_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 19489 ≤ 19489; omega
  · change 19489 ≤ 19500; omega
  · apply DusartPrimeRowsChain.cons
    · change 19501 ≤ 19501; omega
    · change 19501 ≤ 19506; omega
    · apply DusartPrimeRowsChain.cons
      · change 19507 ≤ 19507; omega
      · change 19507 ≤ 19530; omega
      · apply DusartPrimeRowsChain.cons
        · change 19531 ≤ 19531; omega
        · change 19531 ≤ 19540; omega
        · apply DusartPrimeRowsChain.cons
          · change 19541 ≤ 19541; omega
          · change 19541 ≤ 19542; omega
          · apply DusartPrimeRowsChain.cons
            · change 19543 ≤ 19543; omega
            · change 19543 ≤ 19552; omega
            · apply DusartPrimeRowsChain.cons
              · change 19553 ≤ 19553; omega
              · change 19553 ≤ 19558; omega
              · apply DusartPrimeRowsChain.cons
                · change 19559 ≤ 19559; omega
                · change 19559 ≤ 19570; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
