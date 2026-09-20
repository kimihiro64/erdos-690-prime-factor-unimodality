import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 162 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part02_chain :
    DusartPrimeRowsChain 14149 14243 dusartPrimeRows_14051_14766_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 14149 ≤ 14149; omega
  · change 14149 ≤ 14152; omega
  · apply DusartPrimeRowsChain.cons
    · change 14153 ≤ 14153; omega
    · change 14153 ≤ 14158; omega
    · apply DusartPrimeRowsChain.cons
      · change 14159 ≤ 14159; omega
      · change 14159 ≤ 14172; omega
      · apply DusartPrimeRowsChain.cons
        · change 14173 ≤ 14173; omega
        · change 14173 ≤ 14176; omega
        · apply DusartPrimeRowsChain.cons
          · change 14177 ≤ 14177; omega
          · change 14177 ≤ 14196; omega
          · apply DusartPrimeRowsChain.cons
            · change 14197 ≤ 14197; omega
            · change 14197 ≤ 14206; omega
            · apply DusartPrimeRowsChain.cons
              · change 14207 ≤ 14207; omega
              · change 14207 ≤ 14220; omega
              · apply DusartPrimeRowsChain.cons
                · change 14221 ≤ 14221; omega
                · change 14221 ≤ 14242; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
