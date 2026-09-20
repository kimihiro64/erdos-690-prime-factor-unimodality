import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 01 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part01_chain :
    DusartPrimeRowsChain 3275 3331 dusartPrimeRows_3275_3802_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 3275 ≤ 3275; omega
  · change 3275 ≤ 3298; omega
  · apply DusartPrimeRowsChain.cons
    · change 3299 ≤ 3299; omega
    · change 3299 ≤ 3300; omega
    · apply DusartPrimeRowsChain.cons
      · change 3301 ≤ 3301; omega
      · change 3301 ≤ 3306; omega
      · apply DusartPrimeRowsChain.cons
        · change 3307 ≤ 3307; omega
        · change 3307 ≤ 3312; omega
        · apply DusartPrimeRowsChain.cons
          · change 3313 ≤ 3313; omega
          · change 3313 ≤ 3318; omega
          · apply DusartPrimeRowsChain.cons
            · change 3319 ≤ 3319; omega
            · change 3319 ≤ 3322; omega
            · apply DusartPrimeRowsChain.cons
              · change 3323 ≤ 3323; omega
              · change 3323 ≤ 3328; omega
              · apply DusartPrimeRowsChain.cons
                · change 3329 ≤ 3329; omega
                · change 3329 ≤ 3330; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
