import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 166 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part06_chain :
    DusartPrimeRowsChain 14479 14551 dusartPrimeRows_14051_14766_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 14479 ≤ 14479; omega
  · change 14479 ≤ 14488; omega
  · apply DusartPrimeRowsChain.cons
    · change 14489 ≤ 14489; omega
    · change 14489 ≤ 14502; omega
    · apply DusartPrimeRowsChain.cons
      · change 14503 ≤ 14503; omega
      · change 14503 ≤ 14518; omega
      · apply DusartPrimeRowsChain.cons
        · change 14519 ≤ 14519; omega
        · change 14519 ≤ 14532; omega
        · apply DusartPrimeRowsChain.cons
          · change 14533 ≤ 14533; omega
          · change 14533 ≤ 14536; omega
          · apply DusartPrimeRowsChain.cons
            · change 14537 ≤ 14537; omega
            · change 14537 ≤ 14542; omega
            · apply DusartPrimeRowsChain.cons
              · change 14543 ≤ 14543; omega
              · change 14543 ≤ 14548; omega
              · apply DusartPrimeRowsChain.cons
                · change 14549 ≤ 14549; omega
                · change 14549 ≤ 14550; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
