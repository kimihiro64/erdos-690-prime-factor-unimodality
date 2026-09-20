import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 138 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12457 dusartPrimeRows_12097_12712_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 12391 ≤ 12391; omega
  · change 12391 ≤ 12400; omega
  · apply DusartPrimeRowsChain.cons
    · change 12401 ≤ 12401; omega
    · change 12401 ≤ 12408; omega
    · apply DusartPrimeRowsChain.cons
      · change 12409 ≤ 12409; omega
      · change 12409 ≤ 12412; omega
      · apply DusartPrimeRowsChain.cons
        · change 12413 ≤ 12413; omega
        · change 12413 ≤ 12420; omega
        · apply DusartPrimeRowsChain.cons
          · change 12421 ≤ 12421; omega
          · change 12421 ≤ 12432; omega
          · apply DusartPrimeRowsChain.cons
            · change 12433 ≤ 12433; omega
            · change 12433 ≤ 12436; omega
            · apply DusartPrimeRowsChain.cons
              · change 12437 ≤ 12437; omega
              · change 12437 ≤ 12450; omega
              · apply DusartPrimeRowsChain.cons
                · change 12451 ≤ 12451; omega
                · change 12451 ≤ 12456; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
