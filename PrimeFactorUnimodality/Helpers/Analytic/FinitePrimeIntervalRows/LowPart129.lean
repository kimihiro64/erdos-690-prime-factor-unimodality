import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 129 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part04_chain :
    DusartPrimeRowsChain 11783 11833 dusartPrimeRows_11503_12096_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 11783 ≤ 11783; omega
  · change 11783 ≤ 11788; omega
  · apply DusartPrimeRowsChain.cons
    · change 11789 ≤ 11789; omega
    · change 11789 ≤ 11800; omega
    · apply DusartPrimeRowsChain.cons
      · change 11801 ≤ 11801; omega
      · change 11801 ≤ 11806; omega
      · apply DusartPrimeRowsChain.cons
        · change 11807 ≤ 11807; omega
        · change 11807 ≤ 11812; omega
        · apply DusartPrimeRowsChain.cons
          · change 11813 ≤ 11813; omega
          · change 11813 ≤ 11820; omega
          · apply DusartPrimeRowsChain.cons
            · change 11821 ≤ 11821; omega
            · change 11821 ≤ 11826; omega
            · apply DusartPrimeRowsChain.cons
              · change 11827 ≤ 11827; omega
              · change 11827 ≤ 11830; omega
              · apply DusartPrimeRowsChain.cons
                · change 11831 ≤ 11831; omega
                · change 11831 ≤ 11832; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
