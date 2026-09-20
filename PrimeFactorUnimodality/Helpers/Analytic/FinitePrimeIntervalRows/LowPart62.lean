import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 62 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part03_chain :
    DusartPrimeRowsChain 7127 7211 dusartPrimeRows_6977_7332_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 7127 ≤ 7127; omega
  · change 7127 ≤ 7128; omega
  · apply DusartPrimeRowsChain.cons
    · change 7129 ≤ 7129; omega
    · change 7129 ≤ 7150; omega
    · apply DusartPrimeRowsChain.cons
      · change 7151 ≤ 7151; omega
      · change 7151 ≤ 7158; omega
      · apply DusartPrimeRowsChain.cons
        · change 7159 ≤ 7159; omega
        · change 7159 ≤ 7176; omega
        · apply DusartPrimeRowsChain.cons
          · change 7177 ≤ 7177; omega
          · change 7177 ≤ 7186; omega
          · apply DusartPrimeRowsChain.cons
            · change 7187 ≤ 7187; omega
            · change 7187 ≤ 7192; omega
            · apply DusartPrimeRowsChain.cons
              · change 7193 ≤ 7193; omega
              · change 7193 ≤ 7206; omega
              · apply DusartPrimeRowsChain.cons
                · change 7207 ≤ 7207; omega
                · change 7207 ≤ 7210; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
