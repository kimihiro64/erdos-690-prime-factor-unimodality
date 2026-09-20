import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 156 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part05_chain :
    DusartPrimeRowsChain 13691 13751 dusartPrimeRows_13367_14050_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 13691 ≤ 13691; omega
  · change 13691 ≤ 13692; omega
  · apply DusartPrimeRowsChain.cons
    · change 13693 ≤ 13693; omega
    · change 13693 ≤ 13696; omega
    · apply DusartPrimeRowsChain.cons
      · change 13697 ≤ 13697; omega
      · change 13697 ≤ 13708; omega
      · apply DusartPrimeRowsChain.cons
        · change 13709 ≤ 13709; omega
        · change 13709 ≤ 13710; omega
        · apply DusartPrimeRowsChain.cons
          · change 13711 ≤ 13711; omega
          · change 13711 ≤ 13720; omega
          · apply DusartPrimeRowsChain.cons
            · change 13721 ≤ 13721; omega
            · change 13721 ≤ 13722; omega
            · apply DusartPrimeRowsChain.cons
              · change 13723 ≤ 13723; omega
              · change 13723 ≤ 13728; omega
              · apply DusartPrimeRowsChain.cons
                · change 13729 ≤ 13729; omega
                · change 13729 ≤ 13750; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
