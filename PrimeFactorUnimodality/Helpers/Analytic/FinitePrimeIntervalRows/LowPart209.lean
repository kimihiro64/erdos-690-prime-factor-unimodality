import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 209 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part06_chain :
    DusartPrimeRowsChain 22397 22483 dusartPrimeRows_22027_23158_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 22397 ≤ 22397; omega
  · change 22397 ≤ 22408; omega
  · apply DusartPrimeRowsChain.cons
    · change 22409 ≤ 22409; omega
    · change 22409 ≤ 22432; omega
    · apply DusartPrimeRowsChain.cons
      · change 22433 ≤ 22433; omega
      · change 22433 ≤ 22440; omega
      · apply DusartPrimeRowsChain.cons
        · change 22441 ≤ 22441; omega
        · change 22441 ≤ 22446; omega
        · apply DusartPrimeRowsChain.cons
          · change 22447 ≤ 22447; omega
          · change 22447 ≤ 22452; omega
          · apply DusartPrimeRowsChain.cons
            · change 22453 ≤ 22453; omega
            · change 22453 ≤ 22468; omega
            · apply DusartPrimeRowsChain.cons
              · change 22469 ≤ 22469; omega
              · change 22469 ≤ 22480; omega
              · apply DusartPrimeRowsChain.cons
                · change 22481 ≤ 22481; omega
                · change 22481 ≤ 22482; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
