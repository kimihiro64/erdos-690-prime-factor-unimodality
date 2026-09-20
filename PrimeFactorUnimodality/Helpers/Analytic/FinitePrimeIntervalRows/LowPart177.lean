import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 177 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part07_chain :
    DusartPrimeRowsChain 15233 15289 dusartPrimeRows_14767_15526_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 15233 ≤ 15233; omega
  · change 15233 ≤ 15240; omega
  · apply DusartPrimeRowsChain.cons
    · change 15241 ≤ 15241; omega
    · change 15241 ≤ 15258; omega
    · apply DusartPrimeRowsChain.cons
      · change 15259 ≤ 15259; omega
      · change 15259 ≤ 15262; omega
      · apply DusartPrimeRowsChain.cons
        · change 15263 ≤ 15263; omega
        · change 15263 ≤ 15268; omega
        · apply DusartPrimeRowsChain.cons
          · change 15269 ≤ 15269; omega
          · change 15269 ≤ 15270; omega
          · apply DusartPrimeRowsChain.cons
            · change 15271 ≤ 15271; omega
            · change 15271 ≤ 15276; omega
            · apply DusartPrimeRowsChain.cons
              · change 15277 ≤ 15277; omega
              · change 15277 ≤ 15286; omega
              · apply DusartPrimeRowsChain.cons
                · change 15287 ≤ 15287; omega
                · change 15287 ≤ 15288; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
