import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 271 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17159) (q := 17167) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17167) (q := 17183) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17183) (q := 17189) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17189) (q := 17191) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17191) (q := 17203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17203) (q := 17207) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17207) (q := 17209) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17209) (q := 17231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part01_chain :
    DusartPrimeRowsChain 17159 17231 dusartPrimeRows_17159_18040_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 17159 ≤ 17159; omega
  · change 17159 ≤ 17166; omega
  · apply DusartPrimeRowsChain.cons
    · change 17167 ≤ 17167; omega
    · change 17167 ≤ 17182; omega
    · apply DusartPrimeRowsChain.cons
      · change 17183 ≤ 17183; omega
      · change 17183 ≤ 17188; omega
      · apply DusartPrimeRowsChain.cons
        · change 17189 ≤ 17189; omega
        · change 17189 ≤ 17190; omega
        · apply DusartPrimeRowsChain.cons
          · change 17191 ≤ 17191; omega
          · change 17191 ≤ 17202; omega
          · apply DusartPrimeRowsChain.cons
            · change 17203 ≤ 17203; omega
            · change 17203 ≤ 17206; omega
            · apply DusartPrimeRowsChain.cons
              · change 17207 ≤ 17207; omega
              · change 17207 ≤ 17208; omega
              · apply DusartPrimeRowsChain.cons
                · change 17209 ≤ 17209; omega
                · change 17209 ≤ 17230; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
