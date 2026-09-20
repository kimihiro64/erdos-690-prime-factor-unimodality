import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 71 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7793 dusartPrimeRows_7717_8110_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 7717 ≤ 7717; omega
  · change 7717 ≤ 7722; omega
  · apply DusartPrimeRowsChain.cons
    · change 7723 ≤ 7723; omega
    · change 7723 ≤ 7726; omega
    · apply DusartPrimeRowsChain.cons
      · change 7727 ≤ 7727; omega
      · change 7727 ≤ 7740; omega
      · apply DusartPrimeRowsChain.cons
        · change 7741 ≤ 7741; omega
        · change 7741 ≤ 7752; omega
        · apply DusartPrimeRowsChain.cons
          · change 7753 ≤ 7753; omega
          · change 7753 ≤ 7756; omega
          · apply DusartPrimeRowsChain.cons
            · change 7757 ≤ 7757; omega
            · change 7757 ≤ 7758; omega
            · apply DusartPrimeRowsChain.cons
              · change 7759 ≤ 7759; omega
              · change 7759 ≤ 7788; omega
              · apply DusartPrimeRowsChain.cons
                · change 7789 ≤ 7789; omega
                · change 7789 ≤ 7792; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
