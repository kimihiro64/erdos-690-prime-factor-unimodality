import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 120 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part03_chain :
    DusartPrimeRowsChain 11093 11171 dusartPrimeRows_10939_11502_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 11093 ≤ 11093; omega
  · change 11093 ≤ 11112; omega
  · apply DusartPrimeRowsChain.cons
    · change 11113 ≤ 11113; omega
    · change 11113 ≤ 11116; omega
    · apply DusartPrimeRowsChain.cons
      · change 11117 ≤ 11117; omega
      · change 11117 ≤ 11118; omega
      · apply DusartPrimeRowsChain.cons
        · change 11119 ≤ 11119; omega
        · change 11119 ≤ 11130; omega
        · apply DusartPrimeRowsChain.cons
          · change 11131 ≤ 11131; omega
          · change 11131 ≤ 11148; omega
          · apply DusartPrimeRowsChain.cons
            · change 11149 ≤ 11149; omega
            · change 11149 ≤ 11158; omega
            · apply DusartPrimeRowsChain.cons
              · change 11159 ≤ 11159; omega
              · change 11159 ≤ 11160; omega
              · apply DusartPrimeRowsChain.cons
                · change 11161 ≤ 11161; omega
                · change 11161 ≤ 11170; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
