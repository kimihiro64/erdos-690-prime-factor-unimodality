import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 234 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19997) (q := 20011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20011) (q := 20021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20021) (q := 20023) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20023) (q := 20029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20029) (q := 20047) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20047) (q := 20051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20051) (q := 20063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20063) (q := 20071) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part02_chain :
    DusartPrimeRowsChain 19997 20071 dusartPrimeRows_19937_20958_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 19997 ≤ 19997; omega
  · change 19997 ≤ 20010; omega
  · apply DusartPrimeRowsChain.cons
    · change 20011 ≤ 20011; omega
    · change 20011 ≤ 20020; omega
    · apply DusartPrimeRowsChain.cons
      · change 20021 ≤ 20021; omega
      · change 20021 ≤ 20022; omega
      · apply DusartPrimeRowsChain.cons
        · change 20023 ≤ 20023; omega
        · change 20023 ≤ 20028; omega
        · apply DusartPrimeRowsChain.cons
          · change 20029 ≤ 20029; omega
          · change 20029 ≤ 20046; omega
          · apply DusartPrimeRowsChain.cons
            · change 20047 ≤ 20047; omega
            · change 20047 ≤ 20050; omega
            · apply DusartPrimeRowsChain.cons
              · change 20051 ≤ 20051; omega
              · change 20051 ≤ 20062; omega
              · apply DusartPrimeRowsChain.cons
                · change 20063 ≤ 20063; omega
                · change 20063 ≤ 20070; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
