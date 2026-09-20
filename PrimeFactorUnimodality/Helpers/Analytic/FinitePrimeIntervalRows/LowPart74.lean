import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 74 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part04_chain :
    DusartPrimeRowsChain 7937 8039 dusartPrimeRows_7717_8110_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 7937 ≤ 7937; omega
  · change 7937 ≤ 7948; omega
  · apply DusartPrimeRowsChain.cons
    · change 7949 ≤ 7949; omega
    · change 7949 ≤ 7950; omega
    · apply DusartPrimeRowsChain.cons
      · change 7951 ≤ 7951; omega
      · change 7951 ≤ 7962; omega
      · apply DusartPrimeRowsChain.cons
        · change 7963 ≤ 7963; omega
        · change 7963 ≤ 7992; omega
        · apply DusartPrimeRowsChain.cons
          · change 7993 ≤ 7993; omega
          · change 7993 ≤ 8008; omega
          · apply DusartPrimeRowsChain.cons
            · change 8009 ≤ 8009; omega
            · change 8009 ≤ 8010; omega
            · apply DusartPrimeRowsChain.cons
              · change 8011 ≤ 8011; omega
              · change 8011 ≤ 8016; omega
              · apply DusartPrimeRowsChain.cons
                · change 8017 ≤ 8017; omega
                · change 8017 ≤ 8038; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
