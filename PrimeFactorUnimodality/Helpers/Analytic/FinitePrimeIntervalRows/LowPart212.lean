import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 212 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part09_chain :
    DusartPrimeRowsChain 22651 22721 dusartPrimeRows_22027_23158_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 22651 ≤ 22651; omega
  · change 22651 ≤ 22668; omega
  · apply DusartPrimeRowsChain.cons
    · change 22669 ≤ 22669; omega
    · change 22669 ≤ 22678; omega
    · apply DusartPrimeRowsChain.cons
      · change 22679 ≤ 22679; omega
      · change 22679 ≤ 22690; omega
      · apply DusartPrimeRowsChain.cons
        · change 22691 ≤ 22691; omega
        · change 22691 ≤ 22696; omega
        · apply DusartPrimeRowsChain.cons
          · change 22697 ≤ 22697; omega
          · change 22697 ≤ 22698; omega
          · apply DusartPrimeRowsChain.cons
            · change 22699 ≤ 22699; omega
            · change 22699 ≤ 22708; omega
            · apply DusartPrimeRowsChain.cons
              · change 22709 ≤ 22709; omega
              · change 22709 ≤ 22716; omega
              · apply DusartPrimeRowsChain.cons
                · change 22717 ≤ 22717; omega
                · change 22717 ≤ 22720; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
