import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 81 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part05_chain :
    DusartPrimeRowsChain 8419 8501 dusartPrimeRows_8111_8520_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 8419 ≤ 8419; omega
  · change 8419 ≤ 8422; omega
  · apply DusartPrimeRowsChain.cons
    · change 8423 ≤ 8423; omega
    · change 8423 ≤ 8428; omega
    · apply DusartPrimeRowsChain.cons
      · change 8429 ≤ 8429; omega
      · change 8429 ≤ 8430; omega
      · apply DusartPrimeRowsChain.cons
        · change 8431 ≤ 8431; omega
        · change 8431 ≤ 8442; omega
        · apply DusartPrimeRowsChain.cons
          · change 8443 ≤ 8443; omega
          · change 8443 ≤ 8446; omega
          · apply DusartPrimeRowsChain.cons
            · change 8447 ≤ 8447; omega
            · change 8447 ≤ 8460; omega
            · apply DusartPrimeRowsChain.cons
              · change 8461 ≤ 8461; omega
              · change 8461 ≤ 8466; omega
              · apply DusartPrimeRowsChain.cons
                · change 8467 ≤ 8467; omega
                · change 8467 ≤ 8500; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
