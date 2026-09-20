import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 127 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part02_chain :
    DusartPrimeRowsChain 11597 11699 dusartPrimeRows_11503_12096_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 11597 ≤ 11597; omega
  · change 11597 ≤ 11616; omega
  · apply DusartPrimeRowsChain.cons
    · change 11617 ≤ 11617; omega
    · change 11617 ≤ 11620; omega
    · apply DusartPrimeRowsChain.cons
      · change 11621 ≤ 11621; omega
      · change 11621 ≤ 11632; omega
      · apply DusartPrimeRowsChain.cons
        · change 11633 ≤ 11633; omega
        · change 11633 ≤ 11656; omega
        · apply DusartPrimeRowsChain.cons
          · change 11657 ≤ 11657; omega
          · change 11657 ≤ 11676; omega
          · apply DusartPrimeRowsChain.cons
            · change 11677 ≤ 11677; omega
            · change 11677 ≤ 11680; omega
            · apply DusartPrimeRowsChain.cons
              · change 11681 ≤ 11681; omega
              · change 11681 ≤ 11688; omega
              · apply DusartPrimeRowsChain.cons
                · change 11689 ≤ 11689; omega
                · change 11689 ≤ 11698; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
