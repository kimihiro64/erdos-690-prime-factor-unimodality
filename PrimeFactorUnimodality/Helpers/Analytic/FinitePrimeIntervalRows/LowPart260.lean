import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 260 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18097) (q := 18119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18119) (q := 18121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18121) (q := 18127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18127) (q := 18131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18131) (q := 18133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18133) (q := 18143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18143) (q := 18149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18149) (q := 18169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part02_chain :
    DusartPrimeRowsChain 18097 18169 dusartPrimeRows_18041_18958_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 18097 ≤ 18097; omega
  · change 18097 ≤ 18118; omega
  · apply DusartPrimeRowsChain.cons
    · change 18119 ≤ 18119; omega
    · change 18119 ≤ 18120; omega
    · apply DusartPrimeRowsChain.cons
      · change 18121 ≤ 18121; omega
      · change 18121 ≤ 18126; omega
      · apply DusartPrimeRowsChain.cons
        · change 18127 ≤ 18127; omega
        · change 18127 ≤ 18130; omega
        · apply DusartPrimeRowsChain.cons
          · change 18131 ≤ 18131; omega
          · change 18131 ≤ 18132; omega
          · apply DusartPrimeRowsChain.cons
            · change 18133 ≤ 18133; omega
            · change 18133 ≤ 18142; omega
            · apply DusartPrimeRowsChain.cons
              · change 18143 ≤ 18143; omega
              · change 18143 ≤ 18148; omega
              · apply DusartPrimeRowsChain.cons
                · change 18149 ≤ 18149; omega
                · change 18149 ≤ 18168; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
