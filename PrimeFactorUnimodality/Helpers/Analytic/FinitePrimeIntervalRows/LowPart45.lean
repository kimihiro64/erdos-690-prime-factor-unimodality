import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 45 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part02_chain :
    DusartPrimeRowsChain 6073 6133 dusartPrimeRows_6007_6310_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 6073 ≤ 6073; omega
  · change 6073 ≤ 6078; omega
  · apply DusartPrimeRowsChain.cons
    · change 6079 ≤ 6079; omega
    · change 6079 ≤ 6088; omega
    · apply DusartPrimeRowsChain.cons
      · change 6089 ≤ 6089; omega
      · change 6089 ≤ 6090; omega
      · apply DusartPrimeRowsChain.cons
        · change 6091 ≤ 6091; omega
        · change 6091 ≤ 6100; omega
        · apply DusartPrimeRowsChain.cons
          · change 6101 ≤ 6101; omega
          · change 6101 ≤ 6112; omega
          · apply DusartPrimeRowsChain.cons
            · change 6113 ≤ 6113; omega
            · change 6113 ≤ 6120; omega
            · apply DusartPrimeRowsChain.cons
              · change 6121 ≤ 6121; omega
              · change 6121 ≤ 6130; omega
              · apply DusartPrimeRowsChain.cons
                · change 6131 ≤ 6131; omega
                · change 6131 ≤ 6132; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
