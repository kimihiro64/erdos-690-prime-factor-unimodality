import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 280 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17863) (q := 17881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17881) (q := 17891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17891) (q := 17903) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17903) (q := 17909) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17909) (q := 17911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17911) (q := 17921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17921) (q := 17923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17923) (q := 17929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part10_chain :
    DusartPrimeRowsChain 17863 17929 dusartPrimeRows_17159_18040_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 17863 ≤ 17863; omega
  · change 17863 ≤ 17880; omega
  · apply DusartPrimeRowsChain.cons
    · change 17881 ≤ 17881; omega
    · change 17881 ≤ 17890; omega
    · apply DusartPrimeRowsChain.cons
      · change 17891 ≤ 17891; omega
      · change 17891 ≤ 17902; omega
      · apply DusartPrimeRowsChain.cons
        · change 17903 ≤ 17903; omega
        · change 17903 ≤ 17908; omega
        · apply DusartPrimeRowsChain.cons
          · change 17909 ≤ 17909; omega
          · change 17909 ≤ 17910; omega
          · apply DusartPrimeRowsChain.cons
            · change 17911 ≤ 17911; omega
            · change 17911 ≤ 17920; omega
            · apply DusartPrimeRowsChain.cons
              · change 17921 ≤ 17921; omega
              · change 17921 ≤ 17922; omega
              · apply DusartPrimeRowsChain.cons
                · change 17923 ≤ 17923; omega
                · change 17923 ≤ 17928; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
