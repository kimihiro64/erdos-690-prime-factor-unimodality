import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 221 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21107) (q := 21121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21121) (q := 21139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21139) (q := 21143) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21143) (q := 21149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21149) (q := 21157) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21157) (q := 21163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21163) (q := 21169) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21169) (q := 21179) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part03_chain :
    DusartPrimeRowsChain 21107 21179 dusartPrimeRows_20959_22026_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 21107 ≤ 21107; omega
  · change 21107 ≤ 21120; omega
  · apply DusartPrimeRowsChain.cons
    · change 21121 ≤ 21121; omega
    · change 21121 ≤ 21138; omega
    · apply DusartPrimeRowsChain.cons
      · change 21139 ≤ 21139; omega
      · change 21139 ≤ 21142; omega
      · apply DusartPrimeRowsChain.cons
        · change 21143 ≤ 21143; omega
        · change 21143 ≤ 21148; omega
        · apply DusartPrimeRowsChain.cons
          · change 21149 ≤ 21149; omega
          · change 21149 ≤ 21156; omega
          · apply DusartPrimeRowsChain.cons
            · change 21157 ≤ 21157; omega
            · change 21157 ≤ 21162; omega
            · apply DusartPrimeRowsChain.cons
              · change 21163 ≤ 21163; omega
              · change 21163 ≤ 21168; omega
              · apply DusartPrimeRowsChain.cons
                · change 21169 ≤ 21169; omega
                · change 21169 ≤ 21178; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
