import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 27 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part01_chain :
    DusartPrimeRowsChain 4919 4969 dusartPrimeRows_4919_5166_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 4919 ≤ 4919; omega
  · change 4919 ≤ 4930; omega
  · apply DusartPrimeRowsChain.cons
    · change 4931 ≤ 4931; omega
    · change 4931 ≤ 4932; omega
    · apply DusartPrimeRowsChain.cons
      · change 4933 ≤ 4933; omega
      · change 4933 ≤ 4936; omega
      · apply DusartPrimeRowsChain.cons
        · change 4937 ≤ 4937; omega
        · change 4937 ≤ 4942; omega
        · apply DusartPrimeRowsChain.cons
          · change 4943 ≤ 4943; omega
          · change 4943 ≤ 4950; omega
          · apply DusartPrimeRowsChain.cons
            · change 4951 ≤ 4951; omega
            · change 4951 ≤ 4956; omega
            · apply DusartPrimeRowsChain.cons
              · change 4957 ≤ 4957; omega
              · change 4957 ≤ 4966; omega
              · apply DusartPrimeRowsChain.cons
                · change 4967 ≤ 4967; omega
                · change 4967 ≤ 4968; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
