import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 211 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part08_chain :
    DusartPrimeRowsChain 22571 22651 dusartPrimeRows_22027_23158_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 22571 ≤ 22571; omega
  · change 22571 ≤ 22572; omega
  · apply DusartPrimeRowsChain.cons
    · change 22573 ≤ 22573; omega
    · change 22573 ≤ 22612; omega
    · apply DusartPrimeRowsChain.cons
      · change 22613 ≤ 22613; omega
      · change 22613 ≤ 22618; omega
      · apply DusartPrimeRowsChain.cons
        · change 22619 ≤ 22619; omega
        · change 22619 ≤ 22620; omega
        · apply DusartPrimeRowsChain.cons
          · change 22621 ≤ 22621; omega
          · change 22621 ≤ 22636; omega
          · apply DusartPrimeRowsChain.cons
            · change 22637 ≤ 22637; omega
            · change 22637 ≤ 22638; omega
            · apply DusartPrimeRowsChain.cons
              · change 22639 ≤ 22639; omega
              · change 22639 ≤ 22642; omega
              · apply DusartPrimeRowsChain.cons
                · change 22643 ≤ 22643; omega
                · change 22643 ≤ 22650; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
