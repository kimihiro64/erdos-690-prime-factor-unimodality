import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 99 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part03_chain :
    DusartPrimeRowsChain 9539 9629 dusartPrimeRows_9419_9900_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 9539 ≤ 9539; omega
  · change 9539 ≤ 9546; omega
  · apply DusartPrimeRowsChain.cons
    · change 9547 ≤ 9547; omega
    · change 9547 ≤ 9550; omega
    · apply DusartPrimeRowsChain.cons
      · change 9551 ≤ 9551; omega
      · change 9551 ≤ 9586; omega
      · apply DusartPrimeRowsChain.cons
        · change 9587 ≤ 9587; omega
        · change 9587 ≤ 9600; omega
        · apply DusartPrimeRowsChain.cons
          · change 9601 ≤ 9601; omega
          · change 9601 ≤ 9612; omega
          · apply DusartPrimeRowsChain.cons
            · change 9613 ≤ 9613; omega
            · change 9613 ≤ 9618; omega
            · apply DusartPrimeRowsChain.cons
              · change 9619 ≤ 9619; omega
              · change 9619 ≤ 9622; omega
              · apply DusartPrimeRowsChain.cons
                · change 9623 ≤ 9623; omega
                · change 9623 ≤ 9628; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
