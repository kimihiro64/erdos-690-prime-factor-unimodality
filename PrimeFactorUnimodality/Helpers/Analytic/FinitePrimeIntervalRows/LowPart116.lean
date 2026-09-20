import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 116 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part06_chain :
    DusartPrimeRowsChain 10799 10883 dusartPrimeRows_10427_10938_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 10799 ≤ 10799; omega
  · change 10799 ≤ 10830; omega
  · apply DusartPrimeRowsChain.cons
    · change 10831 ≤ 10831; omega
    · change 10831 ≤ 10836; omega
    · apply DusartPrimeRowsChain.cons
      · change 10837 ≤ 10837; omega
      · change 10837 ≤ 10846; omega
      · apply DusartPrimeRowsChain.cons
        · change 10847 ≤ 10847; omega
        · change 10847 ≤ 10852; omega
        · apply DusartPrimeRowsChain.cons
          · change 10853 ≤ 10853; omega
          · change 10853 ≤ 10858; omega
          · apply DusartPrimeRowsChain.cons
            · change 10859 ≤ 10859; omega
            · change 10859 ≤ 10860; omega
            · apply DusartPrimeRowsChain.cons
              · change 10861 ≤ 10861; omega
              · change 10861 ≤ 10866; omega
              · apply DusartPrimeRowsChain.cons
                · change 10867 ≤ 10867; omega
                · change 10867 ≤ 10882; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
