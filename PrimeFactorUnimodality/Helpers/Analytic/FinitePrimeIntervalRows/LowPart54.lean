import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 54 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part01_chain :
    DusartPrimeRowsChain 6637 6701 dusartPrimeRows_6637_6976_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 6637 ≤ 6637; omega
  · change 6637 ≤ 6652; omega
  · apply DusartPrimeRowsChain.cons
    · change 6653 ≤ 6653; omega
    · change 6653 ≤ 6658; omega
    · apply DusartPrimeRowsChain.cons
      · change 6659 ≤ 6659; omega
      · change 6659 ≤ 6660; omega
      · apply DusartPrimeRowsChain.cons
        · change 6661 ≤ 6661; omega
        · change 6661 ≤ 6672; omega
        · apply DusartPrimeRowsChain.cons
          · change 6673 ≤ 6673; omega
          · change 6673 ≤ 6678; omega
          · apply DusartPrimeRowsChain.cons
            · change 6679 ≤ 6679; omega
            · change 6679 ≤ 6688; omega
            · apply DusartPrimeRowsChain.cons
              · change 6689 ≤ 6689; omega
              · change 6689 ≤ 6690; omega
              · apply DusartPrimeRowsChain.cons
                · change 6691 ≤ 6691; omega
                · change 6691 ≤ 6700; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
