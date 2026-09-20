import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 171 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part01_chain :
    DusartPrimeRowsChain 14767 14831 dusartPrimeRows_14767_15526_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 14767 ≤ 14767; omega
  · change 14767 ≤ 14770; omega
  · apply DusartPrimeRowsChain.cons
    · change 14771 ≤ 14771; omega
    · change 14771 ≤ 14778; omega
    · apply DusartPrimeRowsChain.cons
      · change 14779 ≤ 14779; omega
      · change 14779 ≤ 14782; omega
      · apply DusartPrimeRowsChain.cons
        · change 14783 ≤ 14783; omega
        · change 14783 ≤ 14796; omega
        · apply DusartPrimeRowsChain.cons
          · change 14797 ≤ 14797; omega
          · change 14797 ≤ 14812; omega
          · apply DusartPrimeRowsChain.cons
            · change 14813 ≤ 14813; omega
            · change 14813 ≤ 14820; omega
            · apply DusartPrimeRowsChain.cons
              · change 14821 ≤ 14821; omega
              · change 14821 ≤ 14826; omega
              · apply DusartPrimeRowsChain.cons
                · change 14827 ≤ 14827; omega
                · change 14827 ≤ 14830; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
