import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 213 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part10_chain :
    DusartPrimeRowsChain 22721 22787 dusartPrimeRows_22027_23158_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 22721 ≤ 22721; omega
  · change 22721 ≤ 22726; omega
  · apply DusartPrimeRowsChain.cons
    · change 22727 ≤ 22727; omega
    · change 22727 ≤ 22738; omega
    · apply DusartPrimeRowsChain.cons
      · change 22739 ≤ 22739; omega
      · change 22739 ≤ 22740; omega
      · apply DusartPrimeRowsChain.cons
        · change 22741 ≤ 22741; omega
        · change 22741 ≤ 22750; omega
        · apply DusartPrimeRowsChain.cons
          · change 22751 ≤ 22751; omega
          · change 22751 ≤ 22768; omega
          · apply DusartPrimeRowsChain.cons
            · change 22769 ≤ 22769; omega
            · change 22769 ≤ 22776; omega
            · apply DusartPrimeRowsChain.cons
              · change 22777 ≤ 22777; omega
              · change 22777 ≤ 22782; omega
              · apply DusartPrimeRowsChain.cons
                · change 22783 ≤ 22783; omega
                · change 22783 ≤ 22786; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
