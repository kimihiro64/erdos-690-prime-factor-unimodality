import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 261 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18169) (q := 18181) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18181) (q := 18191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18191) (q := 18199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18199) (q := 18211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18211) (q := 18217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18217) (q := 18223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18223) (q := 18229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18229) (q := 18233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part03_chain :
    DusartPrimeRowsChain 18169 18233 dusartPrimeRows_18041_18958_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 18169 ≤ 18169; omega
  · change 18169 ≤ 18180; omega
  · apply DusartPrimeRowsChain.cons
    · change 18181 ≤ 18181; omega
    · change 18181 ≤ 18190; omega
    · apply DusartPrimeRowsChain.cons
      · change 18191 ≤ 18191; omega
      · change 18191 ≤ 18198; omega
      · apply DusartPrimeRowsChain.cons
        · change 18199 ≤ 18199; omega
        · change 18199 ≤ 18210; omega
        · apply DusartPrimeRowsChain.cons
          · change 18211 ≤ 18211; omega
          · change 18211 ≤ 18216; omega
          · apply DusartPrimeRowsChain.cons
            · change 18217 ≤ 18217; omega
            · change 18217 ≤ 18222; omega
            · apply DusartPrimeRowsChain.cons
              · change 18223 ≤ 18223; omega
              · change 18223 ≤ 18228; omega
              · apply DusartPrimeRowsChain.cons
                · change 18229 ≤ 18229; omega
                · change 18229 ≤ 18232; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
