import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 242 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20639) (q := 20641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20641) (q := 20663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20663) (q := 20681) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20681) (q := 20693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20693) (q := 20707) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20707) (q := 20717) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20717) (q := 20719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20719) (q := 20731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part10_chain :
    DusartPrimeRowsChain 20639 20731 dusartPrimeRows_19937_20958_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 20639 ≤ 20639; omega
  · change 20639 ≤ 20640; omega
  · apply DusartPrimeRowsChain.cons
    · change 20641 ≤ 20641; omega
    · change 20641 ≤ 20662; omega
    · apply DusartPrimeRowsChain.cons
      · change 20663 ≤ 20663; omega
      · change 20663 ≤ 20680; omega
      · apply DusartPrimeRowsChain.cons
        · change 20681 ≤ 20681; omega
        · change 20681 ≤ 20692; omega
        · apply DusartPrimeRowsChain.cons
          · change 20693 ≤ 20693; omega
          · change 20693 ≤ 20706; omega
          · apply DusartPrimeRowsChain.cons
            · change 20707 ≤ 20707; omega
            · change 20707 ≤ 20716; omega
            · apply DusartPrimeRowsChain.cons
              · change 20717 ≤ 20717; omega
              · change 20717 ≤ 20718; omega
              · apply DusartPrimeRowsChain.cons
                · change 20719 ≤ 20719; omega
                · change 20719 ≤ 20730; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
