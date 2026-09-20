import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 175 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part05_chain :
    DusartPrimeRowsChain 15083 15149 dusartPrimeRows_14767_15526_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 15083 ≤ 15083; omega
  · change 15083 ≤ 15090; omega
  · apply DusartPrimeRowsChain.cons
    · change 15091 ≤ 15091; omega
    · change 15091 ≤ 15100; omega
    · apply DusartPrimeRowsChain.cons
      · change 15101 ≤ 15101; omega
      · change 15101 ≤ 15106; omega
      · apply DusartPrimeRowsChain.cons
        · change 15107 ≤ 15107; omega
        · change 15107 ≤ 15120; omega
        · apply DusartPrimeRowsChain.cons
          · change 15121 ≤ 15121; omega
          · change 15121 ≤ 15130; omega
          · apply DusartPrimeRowsChain.cons
            · change 15131 ≤ 15131; omega
            · change 15131 ≤ 15136; omega
            · apply DusartPrimeRowsChain.cons
              · change 15137 ≤ 15137; omega
              · change 15137 ≤ 15138; omega
              · apply DusartPrimeRowsChain.cons
                · change 15139 ≤ 15139; omega
                · change 15139 ≤ 15148; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
