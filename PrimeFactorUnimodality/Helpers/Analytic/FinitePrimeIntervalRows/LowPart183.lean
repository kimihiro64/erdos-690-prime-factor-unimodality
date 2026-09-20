import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 183 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part02_chain :
    DusartPrimeRowsChain 15607 15667 dusartPrimeRows_15527_16318_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 15607 ≤ 15607; omega
  · change 15607 ≤ 15618; omega
  · apply DusartPrimeRowsChain.cons
    · change 15619 ≤ 15619; omega
    · change 15619 ≤ 15628; omega
    · apply DusartPrimeRowsChain.cons
      · change 15629 ≤ 15629; omega
      · change 15629 ≤ 15640; omega
      · apply DusartPrimeRowsChain.cons
        · change 15641 ≤ 15641; omega
        · change 15641 ≤ 15642; omega
        · apply DusartPrimeRowsChain.cons
          · change 15643 ≤ 15643; omega
          · change 15643 ≤ 15646; omega
          · apply DusartPrimeRowsChain.cons
            · change 15647 ≤ 15647; omega
            · change 15647 ≤ 15648; omega
            · apply DusartPrimeRowsChain.cons
              · change 15649 ≤ 15649; omega
              · change 15649 ≤ 15660; omega
              · apply DusartPrimeRowsChain.cons
                · change 15661 ≤ 15661; omega
                · change 15661 ≤ 15666; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
