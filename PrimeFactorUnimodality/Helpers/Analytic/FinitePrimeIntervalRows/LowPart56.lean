import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 56 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part03_chain :
    DusartPrimeRowsChain 6779 6833 dusartPrimeRows_6637_6976_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 6779 ≤ 6779; omega
  · change 6779 ≤ 6780; omega
  · apply DusartPrimeRowsChain.cons
    · change 6781 ≤ 6781; omega
    · change 6781 ≤ 6790; omega
    · apply DusartPrimeRowsChain.cons
      · change 6791 ≤ 6791; omega
      · change 6791 ≤ 6792; omega
      · apply DusartPrimeRowsChain.cons
        · change 6793 ≤ 6793; omega
        · change 6793 ≤ 6802; omega
        · apply DusartPrimeRowsChain.cons
          · change 6803 ≤ 6803; omega
          · change 6803 ≤ 6822; omega
          · apply DusartPrimeRowsChain.cons
            · change 6823 ≤ 6823; omega
            · change 6823 ≤ 6826; omega
            · apply DusartPrimeRowsChain.cons
              · change 6827 ≤ 6827; omega
              · change 6827 ≤ 6828; omega
              · apply DusartPrimeRowsChain.cons
                · change 6829 ≤ 6829; omega
                · change 6829 ≤ 6832; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
