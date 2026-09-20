import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 163 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part03_chain :
    DusartPrimeRowsChain 14243 14327 dusartPrimeRows_14051_14766_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 14243 ≤ 14243; omega
  · change 14243 ≤ 14248; omega
  · apply DusartPrimeRowsChain.cons
    · change 14249 ≤ 14249; omega
    · change 14249 ≤ 14250; omega
    · apply DusartPrimeRowsChain.cons
      · change 14251 ≤ 14251; omega
      · change 14251 ≤ 14280; omega
      · apply DusartPrimeRowsChain.cons
        · change 14281 ≤ 14281; omega
        · change 14281 ≤ 14292; omega
        · apply DusartPrimeRowsChain.cons
          · change 14293 ≤ 14293; omega
          · change 14293 ≤ 14302; omega
          · apply DusartPrimeRowsChain.cons
            · change 14303 ≤ 14303; omega
            · change 14303 ≤ 14320; omega
            · apply DusartPrimeRowsChain.cons
              · change 14321 ≤ 14321; omega
              · change 14321 ≤ 14322; omega
              · apply DusartPrimeRowsChain.cons
                · change 14323 ≤ 14323; omega
                · change 14323 ≤ 14326; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
