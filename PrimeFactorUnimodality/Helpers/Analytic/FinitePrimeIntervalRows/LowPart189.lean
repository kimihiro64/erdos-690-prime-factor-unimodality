import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 189 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part08_chain :
    DusartPrimeRowsChain 16063 16111 dusartPrimeRows_15527_16318_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 16063 ≤ 16063; omega
  · change 16063 ≤ 16066; omega
  · apply DusartPrimeRowsChain.cons
    · change 16067 ≤ 16067; omega
    · change 16067 ≤ 16068; omega
    · apply DusartPrimeRowsChain.cons
      · change 16069 ≤ 16069; omega
      · change 16069 ≤ 16072; omega
      · apply DusartPrimeRowsChain.cons
        · change 16073 ≤ 16073; omega
        · change 16073 ≤ 16086; omega
        · apply DusartPrimeRowsChain.cons
          · change 16087 ≤ 16087; omega
          · change 16087 ≤ 16090; omega
          · apply DusartPrimeRowsChain.cons
            · change 16091 ≤ 16091; omega
            · change 16091 ≤ 16096; omega
            · apply DusartPrimeRowsChain.cons
              · change 16097 ≤ 16097; omega
              · change 16097 ≤ 16102; omega
              · apply DusartPrimeRowsChain.cons
                · change 16103 ≤ 16103; omega
                · change 16103 ≤ 16110; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
