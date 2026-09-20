import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 154 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13619 dusartPrimeRows_13367_14050_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 13523 ≤ 13523; omega
  · change 13523 ≤ 13536; omega
  · apply DusartPrimeRowsChain.cons
    · change 13537 ≤ 13537; omega
    · change 13537 ≤ 13552; omega
    · apply DusartPrimeRowsChain.cons
      · change 13553 ≤ 13553; omega
      · change 13553 ≤ 13566; omega
      · apply DusartPrimeRowsChain.cons
        · change 13567 ≤ 13567; omega
        · change 13567 ≤ 13576; omega
        · apply DusartPrimeRowsChain.cons
          · change 13577 ≤ 13577; omega
          · change 13577 ≤ 13590; omega
          · apply DusartPrimeRowsChain.cons
            · change 13591 ≤ 13591; omega
            · change 13591 ≤ 13596; omega
            · apply DusartPrimeRowsChain.cons
              · change 13597 ≤ 13597; omega
              · change 13597 ≤ 13612; omega
              · apply DusartPrimeRowsChain.cons
                · change 13613 ≤ 13613; omega
                · change 13613 ≤ 13618; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
