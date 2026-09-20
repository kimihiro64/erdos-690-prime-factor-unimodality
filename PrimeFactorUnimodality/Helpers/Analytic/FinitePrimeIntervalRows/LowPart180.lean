import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 180 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part10_chain :
    DusartPrimeRowsChain 15427 15497 dusartPrimeRows_14767_15526_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 15427 ≤ 15427; omega
  · change 15427 ≤ 15438; omega
  · apply DusartPrimeRowsChain.cons
    · change 15439 ≤ 15439; omega
    · change 15439 ≤ 15442; omega
    · apply DusartPrimeRowsChain.cons
      · change 15443 ≤ 15443; omega
      · change 15443 ≤ 15450; omega
      · apply DusartPrimeRowsChain.cons
        · change 15451 ≤ 15451; omega
        · change 15451 ≤ 15460; omega
        · apply DusartPrimeRowsChain.cons
          · change 15461 ≤ 15461; omega
          · change 15461 ≤ 15466; omega
          · apply DusartPrimeRowsChain.cons
            · change 15467 ≤ 15467; omega
            · change 15467 ≤ 15472; omega
            · apply DusartPrimeRowsChain.cons
              · change 15473 ≤ 15473; omega
              · change 15473 ≤ 15492; omega
              · apply DusartPrimeRowsChain.cons
                · change 15493 ≤ 15493; omega
                · change 15493 ≤ 15496; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
