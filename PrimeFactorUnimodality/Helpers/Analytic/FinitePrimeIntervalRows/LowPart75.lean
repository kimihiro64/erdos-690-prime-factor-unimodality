import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 75 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part05_chain :
    DusartPrimeRowsChain 8039 8101 dusartPrimeRows_7717_8110_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 8039 ≤ 8039; omega
  · change 8039 ≤ 8052; omega
  · apply DusartPrimeRowsChain.cons
    · change 8053 ≤ 8053; omega
    · change 8053 ≤ 8058; omega
    · apply DusartPrimeRowsChain.cons
      · change 8059 ≤ 8059; omega
      · change 8059 ≤ 8068; omega
      · apply DusartPrimeRowsChain.cons
        · change 8069 ≤ 8069; omega
        · change 8069 ≤ 8080; omega
        · apply DusartPrimeRowsChain.cons
          · change 8081 ≤ 8081; omega
          · change 8081 ≤ 8086; omega
          · apply DusartPrimeRowsChain.cons
            · change 8087 ≤ 8087; omega
            · change 8087 ≤ 8088; omega
            · apply DusartPrimeRowsChain.cons
              · change 8089 ≤ 8089; omega
              · change 8089 ≤ 8092; omega
              · apply DusartPrimeRowsChain.cons
                · change 8093 ≤ 8093; omega
                · change 8093 ≤ 8100; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
