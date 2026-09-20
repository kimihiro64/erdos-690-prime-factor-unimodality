import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 38 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part04_chain :
    DusartPrimeRowsChain 5647 5693 dusartPrimeRows_5437_5710_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 5647 ≤ 5647; omega
  · change 5647 ≤ 5650; omega
  · apply DusartPrimeRowsChain.cons
    · change 5651 ≤ 5651; omega
    · change 5651 ≤ 5652; omega
    · apply DusartPrimeRowsChain.cons
      · change 5653 ≤ 5653; omega
      · change 5653 ≤ 5656; omega
      · apply DusartPrimeRowsChain.cons
        · change 5657 ≤ 5657; omega
        · change 5657 ≤ 5658; omega
        · apply DusartPrimeRowsChain.cons
          · change 5659 ≤ 5659; omega
          · change 5659 ≤ 5668; omega
          · apply DusartPrimeRowsChain.cons
            · change 5669 ≤ 5669; omega
            · change 5669 ≤ 5682; omega
            · apply DusartPrimeRowsChain.cons
              · change 5683 ≤ 5683; omega
              · change 5683 ≤ 5688; omega
              · apply DusartPrimeRowsChain.cons
                · change 5689 ≤ 5689; omega
                · change 5689 ≤ 5692; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
