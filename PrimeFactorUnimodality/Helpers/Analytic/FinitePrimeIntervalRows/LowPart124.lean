import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 124 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part07_chain :
    DusartPrimeRowsChain 11411 11489 dusartPrimeRows_10939_11502_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 11411 ≤ 11411; omega
  · change 11411 ≤ 11422; omega
  · apply DusartPrimeRowsChain.cons
    · change 11423 ≤ 11423; omega
    · change 11423 ≤ 11436; omega
    · apply DusartPrimeRowsChain.cons
      · change 11437 ≤ 11437; omega
      · change 11437 ≤ 11442; omega
      · apply DusartPrimeRowsChain.cons
        · change 11443 ≤ 11443; omega
        · change 11443 ≤ 11446; omega
        · apply DusartPrimeRowsChain.cons
          · change 11447 ≤ 11447; omega
          · change 11447 ≤ 11466; omega
          · apply DusartPrimeRowsChain.cons
            · change 11467 ≤ 11467; omega
            · change 11467 ≤ 11470; omega
            · apply DusartPrimeRowsChain.cons
              · change 11471 ≤ 11471; omega
              · change 11471 ≤ 11482; omega
              · apply DusartPrimeRowsChain.cons
                · change 11483 ≤ 11483; omega
                · change 11483 ≤ 11488; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
