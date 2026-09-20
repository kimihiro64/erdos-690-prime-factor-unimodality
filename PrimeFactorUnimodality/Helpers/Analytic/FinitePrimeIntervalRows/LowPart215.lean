import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 215 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part12_chain :
    DusartPrimeRowsChain 22877 22973 dusartPrimeRows_22027_23158_part12 := by
  apply DusartPrimeRowsChain.cons
  · change 22877 ≤ 22877; omega
  · change 22877 ≤ 22900; omega
  · apply DusartPrimeRowsChain.cons
    · change 22901 ≤ 22901; omega
    · change 22901 ≤ 22906; omega
    · apply DusartPrimeRowsChain.cons
      · change 22907 ≤ 22907; omega
      · change 22907 ≤ 22920; omega
      · apply DusartPrimeRowsChain.cons
        · change 22921 ≤ 22921; omega
        · change 22921 ≤ 22936; omega
        · apply DusartPrimeRowsChain.cons
          · change 22937 ≤ 22937; omega
          · change 22937 ≤ 22942; omega
          · apply DusartPrimeRowsChain.cons
            · change 22943 ≤ 22943; omega
            · change 22943 ≤ 22960; omega
            · apply DusartPrimeRowsChain.cons
              · change 22961 ≤ 22961; omega
              · change 22961 ≤ 22962; omega
              · apply DusartPrimeRowsChain.cons
                · change 22963 ≤ 22963; omega
                · change 22963 ≤ 22972; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
