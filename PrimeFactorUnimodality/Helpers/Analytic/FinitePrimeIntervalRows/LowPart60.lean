import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 60 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part01_chain :
    DusartPrimeRowsChain 6977 7039 dusartPrimeRows_6977_7332_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 6977 ≤ 6977; omega
  · change 6977 ≤ 6982; omega
  · apply DusartPrimeRowsChain.cons
    · change 6983 ≤ 6983; omega
    · change 6983 ≤ 6990; omega
    · apply DusartPrimeRowsChain.cons
      · change 6991 ≤ 6991; omega
      · change 6991 ≤ 6996; omega
      · apply DusartPrimeRowsChain.cons
        · change 6997 ≤ 6997; omega
        · change 6997 ≤ 7000; omega
        · apply DusartPrimeRowsChain.cons
          · change 7001 ≤ 7001; omega
          · change 7001 ≤ 7012; omega
          · apply DusartPrimeRowsChain.cons
            · change 7013 ≤ 7013; omega
            · change 7013 ≤ 7018; omega
            · apply DusartPrimeRowsChain.cons
              · change 7019 ≤ 7019; omega
              · change 7019 ≤ 7026; omega
              · apply DusartPrimeRowsChain.cons
                · change 7027 ≤ 7027; omega
                · change 7027 ≤ 7038; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
