import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 104 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part01_chain :
    DusartPrimeRowsChain 9901 9973 dusartPrimeRows_9901_10426_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 9901 ≤ 9901; omega
  · change 9901 ≤ 9906; omega
  · apply DusartPrimeRowsChain.cons
    · change 9907 ≤ 9907; omega
    · change 9907 ≤ 9922; omega
    · apply DusartPrimeRowsChain.cons
      · change 9923 ≤ 9923; omega
      · change 9923 ≤ 9928; omega
      · apply DusartPrimeRowsChain.cons
        · change 9929 ≤ 9929; omega
        · change 9929 ≤ 9930; omega
        · apply DusartPrimeRowsChain.cons
          · change 9931 ≤ 9931; omega
          · change 9931 ≤ 9940; omega
          · apply DusartPrimeRowsChain.cons
            · change 9941 ≤ 9941; omega
            · change 9941 ≤ 9948; omega
            · apply DusartPrimeRowsChain.cons
              · change 9949 ≤ 9949; omega
              · change 9949 ≤ 9966; omega
              · apply DusartPrimeRowsChain.cons
                · change 9967 ≤ 9967; omega
                · change 9967 ≤ 9972; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
