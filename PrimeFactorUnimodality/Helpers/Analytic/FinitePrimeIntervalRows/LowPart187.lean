import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 187 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part06_chain :
    DusartPrimeRowsChain 15889 15971 dusartPrimeRows_15527_16318_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 15889 ≤ 15889; omega
  · change 15889 ≤ 15900; omega
  · apply DusartPrimeRowsChain.cons
    · change 15901 ≤ 15901; omega
    · change 15901 ≤ 15906; omega
    · apply DusartPrimeRowsChain.cons
      · change 15907 ≤ 15907; omega
      · change 15907 ≤ 15912; omega
      · apply DusartPrimeRowsChain.cons
        · change 15913 ≤ 15913; omega
        · change 15913 ≤ 15918; omega
        · apply DusartPrimeRowsChain.cons
          · change 15919 ≤ 15919; omega
          · change 15919 ≤ 15922; omega
          · apply DusartPrimeRowsChain.cons
            · change 15923 ≤ 15923; omega
            · change 15923 ≤ 15936; omega
            · apply DusartPrimeRowsChain.cons
              · change 15937 ≤ 15937; omega
              · change 15937 ≤ 15958; omega
              · apply DusartPrimeRowsChain.cons
                · change 15959 ≤ 15959; omega
                · change 15959 ≤ 15970; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
