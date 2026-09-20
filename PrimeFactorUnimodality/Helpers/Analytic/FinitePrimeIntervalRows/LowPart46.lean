import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 46 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part03_chain :
    DusartPrimeRowsChain 6133 6211 dusartPrimeRows_6007_6310_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 6133 ≤ 6133; omega
  · change 6133 ≤ 6142; omega
  · apply DusartPrimeRowsChain.cons
    · change 6143 ≤ 6143; omega
    · change 6143 ≤ 6150; omega
    · apply DusartPrimeRowsChain.cons
      · change 6151 ≤ 6151; omega
      · change 6151 ≤ 6162; omega
      · apply DusartPrimeRowsChain.cons
        · change 6163 ≤ 6163; omega
        · change 6163 ≤ 6172; omega
        · apply DusartPrimeRowsChain.cons
          · change 6173 ≤ 6173; omega
          · change 6173 ≤ 6196; omega
          · apply DusartPrimeRowsChain.cons
            · change 6197 ≤ 6197; omega
            · change 6197 ≤ 6198; omega
            · apply DusartPrimeRowsChain.cons
              · change 6199 ≤ 6199; omega
              · change 6199 ≤ 6202; omega
              · apply DusartPrimeRowsChain.cons
                · change 6203 ≤ 6203; omega
                · change 6203 ≤ 6210; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
