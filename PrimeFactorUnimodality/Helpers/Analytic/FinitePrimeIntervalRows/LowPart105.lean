import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 105 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part02_chain :
    DusartPrimeRowsChain 9973 10079 dusartPrimeRows_9901_10426_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 9973 ≤ 9973; omega
  · change 9973 ≤ 10006; omega
  · apply DusartPrimeRowsChain.cons
    · change 10007 ≤ 10007; omega
    · change 10007 ≤ 10008; omega
    · apply DusartPrimeRowsChain.cons
      · change 10009 ≤ 10009; omega
      · change 10009 ≤ 10036; omega
      · apply DusartPrimeRowsChain.cons
        · change 10037 ≤ 10037; omega
        · change 10037 ≤ 10038; omega
        · apply DusartPrimeRowsChain.cons
          · change 10039 ≤ 10039; omega
          · change 10039 ≤ 10060; omega
          · apply DusartPrimeRowsChain.cons
            · change 10061 ≤ 10061; omega
            · change 10061 ≤ 10066; omega
            · apply DusartPrimeRowsChain.cons
              · change 10067 ≤ 10067; omega
              · change 10067 ≤ 10068; omega
              · apply DusartPrimeRowsChain.cons
                · change 10069 ≤ 10069; omega
                · change 10069 ≤ 10078; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
