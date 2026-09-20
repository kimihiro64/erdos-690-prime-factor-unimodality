import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 199 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part07_chain :
    DusartPrimeRowsChain 16823 16901 dusartPrimeRows_16319_17158_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 16823 ≤ 16823; omega
  · change 16823 ≤ 16828; omega
  · apply DusartPrimeRowsChain.cons
    · change 16829 ≤ 16829; omega
    · change 16829 ≤ 16830; omega
    · apply DusartPrimeRowsChain.cons
      · change 16831 ≤ 16831; omega
      · change 16831 ≤ 16842; omega
      · apply DusartPrimeRowsChain.cons
        · change 16843 ≤ 16843; omega
        · change 16843 ≤ 16870; omega
        · apply DusartPrimeRowsChain.cons
          · change 16871 ≤ 16871; omega
          · change 16871 ≤ 16878; omega
          · apply DusartPrimeRowsChain.cons
            · change 16879 ≤ 16879; omega
            · change 16879 ≤ 16882; omega
            · apply DusartPrimeRowsChain.cons
              · change 16883 ≤ 16883; omega
              · change 16883 ≤ 16888; omega
              · apply DusartPrimeRowsChain.cons
                · change 16889 ≤ 16889; omega
                · change 16889 ≤ 16900; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
