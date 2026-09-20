import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 176 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part06_chain :
    DusartPrimeRowsChain 15149 15233 dusartPrimeRows_14767_15526_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 15149 ≤ 15149; omega
  · change 15149 ≤ 15160; omega
  · apply DusartPrimeRowsChain.cons
    · change 15161 ≤ 15161; omega
    · change 15161 ≤ 15172; omega
    · apply DusartPrimeRowsChain.cons
      · change 15173 ≤ 15173; omega
      · change 15173 ≤ 15186; omega
      · apply DusartPrimeRowsChain.cons
        · change 15187 ≤ 15187; omega
        · change 15187 ≤ 15192; omega
        · apply DusartPrimeRowsChain.cons
          · change 15193 ≤ 15193; omega
          · change 15193 ≤ 15198; omega
          · apply DusartPrimeRowsChain.cons
            · change 15199 ≤ 15199; omega
            · change 15199 ≤ 15216; omega
            · apply DusartPrimeRowsChain.cons
              · change 15217 ≤ 15217; omega
              · change 15217 ≤ 15226; omega
              · apply DusartPrimeRowsChain.cons
                · change 15227 ≤ 15227; omega
                · change 15227 ≤ 15232; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
