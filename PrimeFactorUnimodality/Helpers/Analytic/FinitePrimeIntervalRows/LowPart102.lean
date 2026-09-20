import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 102 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part06_chain :
    DusartPrimeRowsChain 9769 9833 dusartPrimeRows_9419_9900_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 9769 ≤ 9769; omega
  · change 9769 ≤ 9780; omega
  · apply DusartPrimeRowsChain.cons
    · change 9781 ≤ 9781; omega
    · change 9781 ≤ 9786; omega
    · apply DusartPrimeRowsChain.cons
      · change 9787 ≤ 9787; omega
      · change 9787 ≤ 9790; omega
      · apply DusartPrimeRowsChain.cons
        · change 9791 ≤ 9791; omega
        · change 9791 ≤ 9802; omega
        · apply DusartPrimeRowsChain.cons
          · change 9803 ≤ 9803; omega
          · change 9803 ≤ 9810; omega
          · apply DusartPrimeRowsChain.cons
            · change 9811 ≤ 9811; omega
            · change 9811 ≤ 9816; omega
            · apply DusartPrimeRowsChain.cons
              · change 9817 ≤ 9817; omega
              · change 9817 ≤ 9828; omega
              · apply DusartPrimeRowsChain.cons
                · change 9829 ≤ 9829; omega
                · change 9829 ≤ 9832; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
