import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 43 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part04_chain :
    DusartPrimeRowsChain 5897 6007 dusartPrimeRows_5711_6006_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 5897 ≤ 5897; omega
  · change 5897 ≤ 5902; omega
  · apply DusartPrimeRowsChain.cons
    · change 5903 ≤ 5903; omega
    · change 5903 ≤ 5922; omega
    · apply DusartPrimeRowsChain.cons
      · change 5923 ≤ 5923; omega
      · change 5923 ≤ 5926; omega
      · apply DusartPrimeRowsChain.cons
        · change 5927 ≤ 5927; omega
        · change 5927 ≤ 5938; omega
        · apply DusartPrimeRowsChain.cons
          · change 5939 ≤ 5939; omega
          · change 5939 ≤ 5952; omega
          · apply DusartPrimeRowsChain.cons
            · change 5953 ≤ 5953; omega
            · change 5953 ≤ 5980; omega
            · apply DusartPrimeRowsChain.cons
              · change 5981 ≤ 5981; omega
              · change 5981 ≤ 5986; omega
              · apply DusartPrimeRowsChain.cons
                · change 5987 ≤ 5987; omega
                · change 5987 ≤ 6006; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
