import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 58 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part05_chain :
    DusartPrimeRowsChain 6907 6971 dusartPrimeRows_6637_6976_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 6907 ≤ 6907; omega
  · change 6907 ≤ 6910; omega
  · apply DusartPrimeRowsChain.cons
    · change 6911 ≤ 6911; omega
    · change 6911 ≤ 6916; omega
    · apply DusartPrimeRowsChain.cons
      · change 6917 ≤ 6917; omega
      · change 6917 ≤ 6946; omega
      · apply DusartPrimeRowsChain.cons
        · change 6947 ≤ 6947; omega
        · change 6947 ≤ 6948; omega
        · apply DusartPrimeRowsChain.cons
          · change 6949 ≤ 6949; omega
          · change 6949 ≤ 6958; omega
          · apply DusartPrimeRowsChain.cons
            · change 6959 ≤ 6959; omega
            · change 6959 ≤ 6960; omega
            · apply DusartPrimeRowsChain.cons
              · change 6961 ≤ 6961; omega
              · change 6961 ≤ 6966; omega
              · apply DusartPrimeRowsChain.cons
                · change 6967 ≤ 6967; omega
                · change 6967 ≤ 6970; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
