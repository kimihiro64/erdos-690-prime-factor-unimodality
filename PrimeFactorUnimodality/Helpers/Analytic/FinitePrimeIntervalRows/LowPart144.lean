import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 144 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12893 dusartPrimeRows_12713_13366_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 12799 ≤ 12799; omega
  · change 12799 ≤ 12808; omega
  · apply DusartPrimeRowsChain.cons
    · change 12809 ≤ 12809; omega
    · change 12809 ≤ 12820; omega
    · apply DusartPrimeRowsChain.cons
      · change 12821 ≤ 12821; omega
      · change 12821 ≤ 12822; omega
      · apply DusartPrimeRowsChain.cons
        · change 12823 ≤ 12823; omega
        · change 12823 ≤ 12828; omega
        · apply DusartPrimeRowsChain.cons
          · change 12829 ≤ 12829; omega
          · change 12829 ≤ 12840; omega
          · apply DusartPrimeRowsChain.cons
            · change 12841 ≤ 12841; omega
            · change 12841 ≤ 12852; omega
            · apply DusartPrimeRowsChain.cons
              · change 12853 ≤ 12853; omega
              · change 12853 ≤ 12888; omega
              · apply DusartPrimeRowsChain.cons
                · change 12889 ≤ 12889; omega
                · change 12889 ≤ 12892; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
