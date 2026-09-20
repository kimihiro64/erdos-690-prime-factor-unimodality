import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 231 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21863) (q := 21871) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21871) (q := 21881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21881) (q := 21893) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21893) (q := 21911) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21911) (q := 21929) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21929) (q := 21937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21937) (q := 21943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21943) (q := 21961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part13_chain :
    DusartPrimeRowsChain 21863 21961 dusartPrimeRows_20959_22026_part13 := by
  apply DusartPrimeRowsChain.cons
  · change 21863 ≤ 21863; omega
  · change 21863 ≤ 21870; omega
  · apply DusartPrimeRowsChain.cons
    · change 21871 ≤ 21871; omega
    · change 21871 ≤ 21880; omega
    · apply DusartPrimeRowsChain.cons
      · change 21881 ≤ 21881; omega
      · change 21881 ≤ 21892; omega
      · apply DusartPrimeRowsChain.cons
        · change 21893 ≤ 21893; omega
        · change 21893 ≤ 21910; omega
        · apply DusartPrimeRowsChain.cons
          · change 21911 ≤ 21911; omega
          · change 21911 ≤ 21928; omega
          · apply DusartPrimeRowsChain.cons
            · change 21929 ≤ 21929; omega
            · change 21929 ≤ 21936; omega
            · apply DusartPrimeRowsChain.cons
              · change 21937 ≤ 21937; omega
              · change 21937 ≤ 21942; omega
              · apply DusartPrimeRowsChain.cons
                · change 21943 ≤ 21943; omega
                · change 21943 ≤ 21960; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
