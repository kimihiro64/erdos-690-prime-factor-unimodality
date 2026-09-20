import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part12_chain :
    DusartPrimeRowsChain 4549 4637 dusartPrimeRows_3803_4672_part12 := by
  apply DusartPrimeRowsChain.cons
  · change 4549 ≤ 4549; omega
  · change 4549 ≤ 4560; omega
  · apply DusartPrimeRowsChain.cons
    · change 4561 ≤ 4561; omega
    · change 4561 ≤ 4566; omega
    · apply DusartPrimeRowsChain.cons
      · change 4567 ≤ 4567; omega
      · change 4567 ≤ 4582; omega
      · apply DusartPrimeRowsChain.cons
        · change 4583 ≤ 4583; omega
        · change 4583 ≤ 4590; omega
        · apply DusartPrimeRowsChain.cons
          · change 4591 ≤ 4591; omega
          · change 4591 ≤ 4596; omega
          · apply DusartPrimeRowsChain.cons
            · change 4597 ≤ 4597; omega
            · change 4597 ≤ 4602; omega
            · apply DusartPrimeRowsChain.cons
              · change 4603 ≤ 4603; omega
              · change 4603 ≤ 4620; omega
              · apply DusartPrimeRowsChain.cons
                · change 4621 ≤ 4621; omega
                · change 4621 ≤ 4636; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
