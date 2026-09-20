import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 251 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19391) (q := 19403) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19403) (q := 19417) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19417) (q := 19421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19421) (q := 19423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19423) (q := 19427) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19427) (q := 19429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19429) (q := 19433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19433) (q := 19441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part06_chain :
    DusartPrimeRowsChain 19391 19441 dusartPrimeRows_18959_19936_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 19391 ≤ 19391; omega
  · change 19391 ≤ 19402; omega
  · apply DusartPrimeRowsChain.cons
    · change 19403 ≤ 19403; omega
    · change 19403 ≤ 19416; omega
    · apply DusartPrimeRowsChain.cons
      · change 19417 ≤ 19417; omega
      · change 19417 ≤ 19420; omega
      · apply DusartPrimeRowsChain.cons
        · change 19421 ≤ 19421; omega
        · change 19421 ≤ 19422; omega
        · apply DusartPrimeRowsChain.cons
          · change 19423 ≤ 19423; omega
          · change 19423 ≤ 19426; omega
          · apply DusartPrimeRowsChain.cons
            · change 19427 ≤ 19427; omega
            · change 19427 ≤ 19428; omega
            · apply DusartPrimeRowsChain.cons
              · change 19429 ≤ 19429; omega
              · change 19429 ≤ 19432; omega
              · apply DusartPrimeRowsChain.cons
                · change 19433 ≤ 19433; omega
                · change 19433 ≤ 19440; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
