import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 182 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part01_chain :
    DusartPrimeRowsChain 15527 15607 dusartPrimeRows_15527_16318_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 15527 ≤ 15527; omega
  · change 15527 ≤ 15540; omega
  · apply DusartPrimeRowsChain.cons
    · change 15541 ≤ 15541; omega
    · change 15541 ≤ 15550; omega
    · apply DusartPrimeRowsChain.cons
      · change 15551 ≤ 15551; omega
      · change 15551 ≤ 15558; omega
      · apply DusartPrimeRowsChain.cons
        · change 15559 ≤ 15559; omega
        · change 15559 ≤ 15568; omega
        · apply DusartPrimeRowsChain.cons
          · change 15569 ≤ 15569; omega
          · change 15569 ≤ 15580; omega
          · apply DusartPrimeRowsChain.cons
            · change 15581 ≤ 15581; omega
            · change 15581 ≤ 15582; omega
            · apply DusartPrimeRowsChain.cons
              · change 15583 ≤ 15583; omega
              · change 15583 ≤ 15600; omega
              · apply DusartPrimeRowsChain.cons
                · change 15601 ≤ 15601; omega
                · change 15601 ≤ 15606; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
