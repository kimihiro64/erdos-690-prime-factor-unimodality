import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 172 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14831 14897 dusartPrimeRows_14767_15526_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 14831 ≤ 14831; omega
  · change 14831 ≤ 14842; omega
  · apply DusartPrimeRowsChain.cons
    · change 14843 ≤ 14843; omega
    · change 14843 ≤ 14850; omega
    · apply DusartPrimeRowsChain.cons
      · change 14851 ≤ 14851; omega
      · change 14851 ≤ 14866; omega
      · apply DusartPrimeRowsChain.cons
        · change 14867 ≤ 14867; omega
        · change 14867 ≤ 14868; omega
        · apply DusartPrimeRowsChain.cons
          · change 14869 ≤ 14869; omega
          · change 14869 ≤ 14878; omega
          · apply DusartPrimeRowsChain.cons
            · change 14879 ≤ 14879; omega
            · change 14879 ≤ 14886; omega
            · apply DusartPrimeRowsChain.cons
              · change 14887 ≤ 14887; omega
              · change 14887 ≤ 14890; omega
              · apply DusartPrimeRowsChain.cons
                · change 14891 ≤ 14891; omega
                · change 14891 ≤ 14896; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
