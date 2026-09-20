import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 23 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part01_chain :
    DusartPrimeRowsChain 4673 4751 dusartPrimeRows_4673_4918_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 4673 ≤ 4673; omega
  · change 4673 ≤ 4678; omega
  · apply DusartPrimeRowsChain.cons
    · change 4679 ≤ 4679; omega
    · change 4679 ≤ 4690; omega
    · apply DusartPrimeRowsChain.cons
      · change 4691 ≤ 4691; omega
      · change 4691 ≤ 4702; omega
      · apply DusartPrimeRowsChain.cons
        · change 4703 ≤ 4703; omega
        · change 4703 ≤ 4720; omega
        · apply DusartPrimeRowsChain.cons
          · change 4721 ≤ 4721; omega
          · change 4721 ≤ 4722; omega
          · apply DusartPrimeRowsChain.cons
            · change 4723 ≤ 4723; omega
            · change 4723 ≤ 4728; omega
            · apply DusartPrimeRowsChain.cons
              · change 4729 ≤ 4729; omega
              · change 4729 ≤ 4732; omega
              · apply DusartPrimeRowsChain.cons
                · change 4733 ≤ 4733; omega
                · change 4733 ≤ 4750; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
