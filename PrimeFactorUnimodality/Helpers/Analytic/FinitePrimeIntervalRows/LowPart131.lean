import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 131 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part06_chain :
    DusartPrimeRowsChain 11923 11971 dusartPrimeRows_11503_12096_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 11923 ≤ 11923; omega
  · change 11923 ≤ 11926; omega
  · apply DusartPrimeRowsChain.cons
    · change 11927 ≤ 11927; omega
    · change 11927 ≤ 11932; omega
    · apply DusartPrimeRowsChain.cons
      · change 11933 ≤ 11933; omega
      · change 11933 ≤ 11938; omega
      · apply DusartPrimeRowsChain.cons
        · change 11939 ≤ 11939; omega
        · change 11939 ≤ 11940; omega
        · apply DusartPrimeRowsChain.cons
          · change 11941 ≤ 11941; omega
          · change 11941 ≤ 11952; omega
          · apply DusartPrimeRowsChain.cons
            · change 11953 ≤ 11953; omega
            · change 11953 ≤ 11958; omega
            · apply DusartPrimeRowsChain.cons
              · change 11959 ≤ 11959; omega
              · change 11959 ≤ 11968; omega
              · apply DusartPrimeRowsChain.cons
                · change 11969 ≤ 11969; omega
                · change 11969 ≤ 11970; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
