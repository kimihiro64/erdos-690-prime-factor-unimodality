import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 259 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18041) (q := 18043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18043) (q := 18047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18047) (q := 18049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18049) (q := 18059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18059) (q := 18061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18061) (q := 18077) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18077) (q := 18089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18089) (q := 18097) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part01_chain :
    DusartPrimeRowsChain 18041 18097 dusartPrimeRows_18041_18958_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 18041 ≤ 18041; omega
  · change 18041 ≤ 18042; omega
  · apply DusartPrimeRowsChain.cons
    · change 18043 ≤ 18043; omega
    · change 18043 ≤ 18046; omega
    · apply DusartPrimeRowsChain.cons
      · change 18047 ≤ 18047; omega
      · change 18047 ≤ 18048; omega
      · apply DusartPrimeRowsChain.cons
        · change 18049 ≤ 18049; omega
        · change 18049 ≤ 18058; omega
        · apply DusartPrimeRowsChain.cons
          · change 18059 ≤ 18059; omega
          · change 18059 ≤ 18060; omega
          · apply DusartPrimeRowsChain.cons
            · change 18061 ≤ 18061; omega
            · change 18061 ≤ 18076; omega
            · apply DusartPrimeRowsChain.cons
              · change 18077 ≤ 18077; omega
              · change 18077 ≤ 18088; omega
              · apply DusartPrimeRowsChain.cons
                · change 18089 ≤ 18089; omega
                · change 18089 ≤ 18096; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
