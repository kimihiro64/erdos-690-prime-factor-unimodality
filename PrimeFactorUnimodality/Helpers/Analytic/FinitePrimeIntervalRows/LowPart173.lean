import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 173 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 14897 14983 dusartPrimeRows_14767_15526_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 14897 ≤ 14897; omega
  · change 14897 ≤ 14922; omega
  · apply DusartPrimeRowsChain.cons
    · change 14923 ≤ 14923; omega
    · change 14923 ≤ 14928; omega
    · apply DusartPrimeRowsChain.cons
      · change 14929 ≤ 14929; omega
      · change 14929 ≤ 14938; omega
      · apply DusartPrimeRowsChain.cons
        · change 14939 ≤ 14939; omega
        · change 14939 ≤ 14946; omega
        · apply DusartPrimeRowsChain.cons
          · change 14947 ≤ 14947; omega
          · change 14947 ≤ 14950; omega
          · apply DusartPrimeRowsChain.cons
            · change 14951 ≤ 14951; omega
            · change 14951 ≤ 14956; omega
            · apply DusartPrimeRowsChain.cons
              · change 14957 ≤ 14957; omega
              · change 14957 ≤ 14968; omega
              · apply DusartPrimeRowsChain.cons
                · change 14969 ≤ 14969; omega
                · change 14969 ≤ 14982; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
