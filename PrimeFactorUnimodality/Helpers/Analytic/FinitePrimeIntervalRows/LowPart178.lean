import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 178 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part08_chain :
    DusartPrimeRowsChain 15289 15359 dusartPrimeRows_14767_15526_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 15289 ≤ 15289; omega
  · change 15289 ≤ 15298; omega
  · apply DusartPrimeRowsChain.cons
    · change 15299 ≤ 15299; omega
    · change 15299 ≤ 15306; omega
    · apply DusartPrimeRowsChain.cons
      · change 15307 ≤ 15307; omega
      · change 15307 ≤ 15312; omega
      · apply DusartPrimeRowsChain.cons
        · change 15313 ≤ 15313; omega
        · change 15313 ≤ 15318; omega
        · apply DusartPrimeRowsChain.cons
          · change 15319 ≤ 15319; omega
          · change 15319 ≤ 15328; omega
          · apply DusartPrimeRowsChain.cons
            · change 15329 ≤ 15329; omega
            · change 15329 ≤ 15330; omega
            · apply DusartPrimeRowsChain.cons
              · change 15331 ≤ 15331; omega
              · change 15331 ≤ 15348; omega
              · apply DusartPrimeRowsChain.cons
                · change 15349 ≤ 15349; omega
                · change 15349 ≤ 15358; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
