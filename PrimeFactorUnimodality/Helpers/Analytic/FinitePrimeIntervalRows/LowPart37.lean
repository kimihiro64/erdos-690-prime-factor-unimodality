import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 37 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part03_chain :
    DusartPrimeRowsChain 5563 5647 dusartPrimeRows_5437_5710_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 5563 ≤ 5563; omega
  · change 5563 ≤ 5568; omega
  · apply DusartPrimeRowsChain.cons
    · change 5569 ≤ 5569; omega
    · change 5569 ≤ 5572; omega
    · apply DusartPrimeRowsChain.cons
      · change 5573 ≤ 5573; omega
      · change 5573 ≤ 5580; omega
      · apply DusartPrimeRowsChain.cons
        · change 5581 ≤ 5581; omega
        · change 5581 ≤ 5590; omega
        · apply DusartPrimeRowsChain.cons
          · change 5591 ≤ 5591; omega
          · change 5591 ≤ 5622; omega
          · apply DusartPrimeRowsChain.cons
            · change 5623 ≤ 5623; omega
            · change 5623 ≤ 5638; omega
            · apply DusartPrimeRowsChain.cons
              · change 5639 ≤ 5639; omega
              · change 5639 ≤ 5640; omega
              · apply DusartPrimeRowsChain.cons
                · change 5641 ≤ 5641; omega
                · change 5641 ≤ 5646; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
