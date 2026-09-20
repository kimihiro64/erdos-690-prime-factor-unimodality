import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 97 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part01_chain :
    DusartPrimeRowsChain 9419 9467 dusartPrimeRows_9419_9900_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 9419 ≤ 9419; omega
  · change 9419 ≤ 9420; omega
  · apply DusartPrimeRowsChain.cons
    · change 9421 ≤ 9421; omega
    · change 9421 ≤ 9430; omega
    · apply DusartPrimeRowsChain.cons
      · change 9431 ≤ 9431; omega
      · change 9431 ≤ 9432; omega
      · apply DusartPrimeRowsChain.cons
        · change 9433 ≤ 9433; omega
        · change 9433 ≤ 9436; omega
        · apply DusartPrimeRowsChain.cons
          · change 9437 ≤ 9437; omega
          · change 9437 ≤ 9438; omega
          · apply DusartPrimeRowsChain.cons
            · change 9439 ≤ 9439; omega
            · change 9439 ≤ 9460; omega
            · apply DusartPrimeRowsChain.cons
              · change 9461 ≤ 9461; omega
              · change 9461 ≤ 9462; omega
              · apply DusartPrimeRowsChain.cons
                · change 9463 ≤ 9463; omega
                · change 9463 ≤ 9466; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
