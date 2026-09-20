import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 55 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part02_chain :
    DusartPrimeRowsChain 6701 6779 dusartPrimeRows_6637_6976_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 6701 ≤ 6701; omega
  · change 6701 ≤ 6702; omega
  · apply DusartPrimeRowsChain.cons
    · change 6703 ≤ 6703; omega
    · change 6703 ≤ 6708; omega
    · apply DusartPrimeRowsChain.cons
      · change 6709 ≤ 6709; omega
      · change 6709 ≤ 6718; omega
      · apply DusartPrimeRowsChain.cons
        · change 6719 ≤ 6719; omega
        · change 6719 ≤ 6732; omega
        · apply DusartPrimeRowsChain.cons
          · change 6733 ≤ 6733; omega
          · change 6733 ≤ 6736; omega
          · apply DusartPrimeRowsChain.cons
            · change 6737 ≤ 6737; omega
            · change 6737 ≤ 6760; omega
            · apply DusartPrimeRowsChain.cons
              · change 6761 ≤ 6761; omega
              · change 6761 ≤ 6762; omega
              · apply DusartPrimeRowsChain.cons
                · change 6763 ≤ 6763; omega
                · change 6763 ≤ 6778; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
