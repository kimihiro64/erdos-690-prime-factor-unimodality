import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 02 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part02_chain :
    DusartPrimeRowsChain 3331 3391 dusartPrimeRows_3275_3802_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 3331 ≤ 3331; omega
  · change 3331 ≤ 3342; omega
  · apply DusartPrimeRowsChain.cons
    · change 3343 ≤ 3343; omega
    · change 3343 ≤ 3346; omega
    · apply DusartPrimeRowsChain.cons
      · change 3347 ≤ 3347; omega
      · change 3347 ≤ 3358; omega
      · apply DusartPrimeRowsChain.cons
        · change 3359 ≤ 3359; omega
        · change 3359 ≤ 3360; omega
        · apply DusartPrimeRowsChain.cons
          · change 3361 ≤ 3361; omega
          · change 3361 ≤ 3370; omega
          · apply DusartPrimeRowsChain.cons
            · change 3371 ≤ 3371; omega
            · change 3371 ≤ 3372; omega
            · apply DusartPrimeRowsChain.cons
              · change 3373 ≤ 3373; omega
              · change 3373 ≤ 3388; omega
              · apply DusartPrimeRowsChain.cons
                · change 3389 ≤ 3389; omega
                · change 3389 ≤ 3390; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
