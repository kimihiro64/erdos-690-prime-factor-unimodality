import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 69 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part05_chain :
    DusartPrimeRowsChain 7607 7687 dusartPrimeRows_7333_7716_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 7607 ≤ 7607; omega
  · change 7607 ≤ 7620; omega
  · apply DusartPrimeRowsChain.cons
    · change 7621 ≤ 7621; omega
    · change 7621 ≤ 7638; omega
    · apply DusartPrimeRowsChain.cons
      · change 7639 ≤ 7639; omega
      · change 7639 ≤ 7642; omega
      · apply DusartPrimeRowsChain.cons
        · change 7643 ≤ 7643; omega
        · change 7643 ≤ 7648; omega
        · apply DusartPrimeRowsChain.cons
          · change 7649 ≤ 7649; omega
          · change 7649 ≤ 7668; omega
          · apply DusartPrimeRowsChain.cons
            · change 7669 ≤ 7669; omega
            · change 7669 ≤ 7672; omega
            · apply DusartPrimeRowsChain.cons
              · change 7673 ≤ 7673; omega
              · change 7673 ≤ 7680; omega
              · apply DusartPrimeRowsChain.cons
                · change 7681 ≤ 7681; omega
                · change 7681 ≤ 7686; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
