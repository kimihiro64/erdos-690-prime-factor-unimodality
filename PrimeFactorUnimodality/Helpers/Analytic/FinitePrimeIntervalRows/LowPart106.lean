import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 106 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part03_chain :
    DusartPrimeRowsChain 10079 10141 dusartPrimeRows_9901_10426_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 10079 ≤ 10079; omega
  · change 10079 ≤ 10090; omega
  · apply DusartPrimeRowsChain.cons
    · change 10091 ≤ 10091; omega
    · change 10091 ≤ 10092; omega
    · apply DusartPrimeRowsChain.cons
      · change 10093 ≤ 10093; omega
      · change 10093 ≤ 10098; omega
      · apply DusartPrimeRowsChain.cons
        · change 10099 ≤ 10099; omega
        · change 10099 ≤ 10102; omega
        · apply DusartPrimeRowsChain.cons
          · change 10103 ≤ 10103; omega
          · change 10103 ≤ 10110; omega
          · apply DusartPrimeRowsChain.cons
            · change 10111 ≤ 10111; omega
            · change 10111 ≤ 10132; omega
            · apply DusartPrimeRowsChain.cons
              · change 10133 ≤ 10133; omega
              · change 10133 ≤ 10138; omega
              · apply DusartPrimeRowsChain.cons
                · change 10139 ≤ 10139; omega
                · change 10139 ≤ 10140; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
