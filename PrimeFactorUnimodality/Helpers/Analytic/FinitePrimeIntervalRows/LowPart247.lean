import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 247 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19051) (q := 19069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19069) (q := 19073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19073) (q := 19079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19079) (q := 19081) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19081) (q := 19087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19087) (q := 19121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19121) (q := 19139) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19139) (q := 19141) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part02_chain :
    DusartPrimeRowsChain 19051 19141 dusartPrimeRows_18959_19936_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 19051 ≤ 19051; omega
  · change 19051 ≤ 19068; omega
  · apply DusartPrimeRowsChain.cons
    · change 19069 ≤ 19069; omega
    · change 19069 ≤ 19072; omega
    · apply DusartPrimeRowsChain.cons
      · change 19073 ≤ 19073; omega
      · change 19073 ≤ 19078; omega
      · apply DusartPrimeRowsChain.cons
        · change 19079 ≤ 19079; omega
        · change 19079 ≤ 19080; omega
        · apply DusartPrimeRowsChain.cons
          · change 19081 ≤ 19081; omega
          · change 19081 ≤ 19086; omega
          · apply DusartPrimeRowsChain.cons
            · change 19087 ≤ 19087; omega
            · change 19087 ≤ 19120; omega
            · apply DusartPrimeRowsChain.cons
              · change 19121 ≤ 19121; omega
              · change 19121 ≤ 19138; omega
              · apply DusartPrimeRowsChain.cons
                · change 19139 ≤ 19139; omega
                · change 19139 ≤ 19140; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
