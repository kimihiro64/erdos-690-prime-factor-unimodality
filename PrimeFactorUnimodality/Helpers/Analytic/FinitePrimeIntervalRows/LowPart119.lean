import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 119 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part02_chain :
    DusartPrimeRowsChain 11027 11093 dusartPrimeRows_10939_11502_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 11027 ≤ 11027; omega
  · change 11027 ≤ 11046; omega
  · apply DusartPrimeRowsChain.cons
    · change 11047 ≤ 11047; omega
    · change 11047 ≤ 11056; omega
    · apply DusartPrimeRowsChain.cons
      · change 11057 ≤ 11057; omega
      · change 11057 ≤ 11058; omega
      · apply DusartPrimeRowsChain.cons
        · change 11059 ≤ 11059; omega
        · change 11059 ≤ 11068; omega
        · apply DusartPrimeRowsChain.cons
          · change 11069 ≤ 11069; omega
          · change 11069 ≤ 11070; omega
          · apply DusartPrimeRowsChain.cons
            · change 11071 ≤ 11071; omega
            · change 11071 ≤ 11082; omega
            · apply DusartPrimeRowsChain.cons
              · change 11083 ≤ 11083; omega
              · change 11083 ≤ 11086; omega
              · apply DusartPrimeRowsChain.cons
                · change 11087 ≤ 11087; omega
                · change 11087 ≤ 11092; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
