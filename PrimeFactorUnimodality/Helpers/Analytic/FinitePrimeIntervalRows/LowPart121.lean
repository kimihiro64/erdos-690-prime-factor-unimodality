import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 121 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part04_chain :
    DusartPrimeRowsChain 11171 11257 dusartPrimeRows_10939_11502_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 11171 ≤ 11171; omega
  · change 11171 ≤ 11172; omega
  · apply DusartPrimeRowsChain.cons
    · change 11173 ≤ 11173; omega
    · change 11173 ≤ 11176; omega
    · apply DusartPrimeRowsChain.cons
      · change 11177 ≤ 11177; omega
      · change 11177 ≤ 11196; omega
      · apply DusartPrimeRowsChain.cons
        · change 11197 ≤ 11197; omega
        · change 11197 ≤ 11212; omega
        · apply DusartPrimeRowsChain.cons
          · change 11213 ≤ 11213; omega
          · change 11213 ≤ 11238; omega
          · apply DusartPrimeRowsChain.cons
            · change 11239 ≤ 11239; omega
            · change 11239 ≤ 11242; omega
            · apply DusartPrimeRowsChain.cons
              · change 11243 ≤ 11243; omega
              · change 11243 ≤ 11250; omega
              · apply DusartPrimeRowsChain.cons
                · change 11251 ≤ 11251; omega
                · change 11251 ≤ 11256; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
