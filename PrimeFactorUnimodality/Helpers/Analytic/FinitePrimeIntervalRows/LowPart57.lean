import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 57 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part04_chain :
    DusartPrimeRowsChain 6833 6907 dusartPrimeRows_6637_6976_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 6833 ≤ 6833; omega
  · change 6833 ≤ 6840; omega
  · apply DusartPrimeRowsChain.cons
    · change 6841 ≤ 6841; omega
    · change 6841 ≤ 6856; omega
    · apply DusartPrimeRowsChain.cons
      · change 6857 ≤ 6857; omega
      · change 6857 ≤ 6862; omega
      · apply DusartPrimeRowsChain.cons
        · change 6863 ≤ 6863; omega
        · change 6863 ≤ 6868; omega
        · apply DusartPrimeRowsChain.cons
          · change 6869 ≤ 6869; omega
          · change 6869 ≤ 6870; omega
          · apply DusartPrimeRowsChain.cons
            · change 6871 ≤ 6871; omega
            · change 6871 ≤ 6882; omega
            · apply DusartPrimeRowsChain.cons
              · change 6883 ≤ 6883; omega
              · change 6883 ≤ 6898; omega
              · apply DusartPrimeRowsChain.cons
                · change 6899 ≤ 6899; omega
                · change 6899 ≤ 6906; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
