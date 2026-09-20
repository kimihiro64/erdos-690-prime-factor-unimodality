import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 130 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part05_chain :
    DusartPrimeRowsChain 11833 11923 dusartPrimeRows_11503_12096_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 11833 ≤ 11833; omega
  · change 11833 ≤ 11838; omega
  · apply DusartPrimeRowsChain.cons
    · change 11839 ≤ 11839; omega
    · change 11839 ≤ 11862; omega
    · apply DusartPrimeRowsChain.cons
      · change 11863 ≤ 11863; omega
      · change 11863 ≤ 11866; omega
      · apply DusartPrimeRowsChain.cons
        · change 11867 ≤ 11867; omega
        · change 11867 ≤ 11886; omega
        · apply DusartPrimeRowsChain.cons
          · change 11887 ≤ 11887; omega
          · change 11887 ≤ 11896; omega
          · apply DusartPrimeRowsChain.cons
            · change 11897 ≤ 11897; omega
            · change 11897 ≤ 11902; omega
            · apply DusartPrimeRowsChain.cons
              · change 11903 ≤ 11903; omega
              · change 11903 ≤ 11908; omega
              · apply DusartPrimeRowsChain.cons
                · change 11909 ≤ 11909; omega
                · change 11909 ≤ 11922; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
