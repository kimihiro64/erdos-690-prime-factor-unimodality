import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 126 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part01_chain :
    DusartPrimeRowsChain 11503 11597 dusartPrimeRows_11503_12096_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 11503 ≤ 11503; omega
  · change 11503 ≤ 11518; omega
  · apply DusartPrimeRowsChain.cons
    · change 11519 ≤ 11519; omega
    · change 11519 ≤ 11526; omega
    · apply DusartPrimeRowsChain.cons
      · change 11527 ≤ 11527; omega
      · change 11527 ≤ 11548; omega
      · apply DusartPrimeRowsChain.cons
        · change 11549 ≤ 11549; omega
        · change 11549 ≤ 11550; omega
        · apply DusartPrimeRowsChain.cons
          · change 11551 ≤ 11551; omega
          · change 11551 ≤ 11578; omega
          · apply DusartPrimeRowsChain.cons
            · change 11579 ≤ 11579; omega
            · change 11579 ≤ 11586; omega
            · apply DusartPrimeRowsChain.cons
              · change 11587 ≤ 11587; omega
              · change 11587 ≤ 11592; omega
              · apply DusartPrimeRowsChain.cons
                · change 11593 ≤ 11593; omega
                · change 11593 ≤ 11596; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
