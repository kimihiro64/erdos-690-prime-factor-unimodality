import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 115 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part05_chain :
    DusartPrimeRowsChain 10723 10799 dusartPrimeRows_10427_10938_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 10723 ≤ 10723; omega
  · change 10723 ≤ 10728; omega
  · apply DusartPrimeRowsChain.cons
    · change 10729 ≤ 10729; omega
    · change 10729 ≤ 10732; omega
    · apply DusartPrimeRowsChain.cons
      · change 10733 ≤ 10733; omega
      · change 10733 ≤ 10738; omega
      · apply DusartPrimeRowsChain.cons
        · change 10739 ≤ 10739; omega
        · change 10739 ≤ 10752; omega
        · apply DusartPrimeRowsChain.cons
          · change 10753 ≤ 10753; omega
          · change 10753 ≤ 10770; omega
          · apply DusartPrimeRowsChain.cons
            · change 10771 ≤ 10771; omega
            · change 10771 ≤ 10780; omega
            · apply DusartPrimeRowsChain.cons
              · change 10781 ≤ 10781; omega
              · change 10781 ≤ 10788; omega
              · apply DusartPrimeRowsChain.cons
                · change 10789 ≤ 10789; omega
                · change 10789 ≤ 10798; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
