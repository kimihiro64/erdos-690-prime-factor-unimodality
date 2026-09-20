import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 135 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part02_chain :
    DusartPrimeRowsChain 12157 12241 dusartPrimeRows_12097_12712_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 12157 ≤ 12157; omega
  · change 12157 ≤ 12160; omega
  · apply DusartPrimeRowsChain.cons
    · change 12161 ≤ 12161; omega
    · change 12161 ≤ 12162; omega
    · apply DusartPrimeRowsChain.cons
      · change 12163 ≤ 12163; omega
      · change 12163 ≤ 12196; omega
      · apply DusartPrimeRowsChain.cons
        · change 12197 ≤ 12197; omega
        · change 12197 ≤ 12202; omega
        · apply DusartPrimeRowsChain.cons
          · change 12203 ≤ 12203; omega
          · change 12203 ≤ 12210; omega
          · apply DusartPrimeRowsChain.cons
            · change 12211 ≤ 12211; omega
            · change 12211 ≤ 12226; omega
            · apply DusartPrimeRowsChain.cons
              · change 12227 ≤ 12227; omega
              · change 12227 ≤ 12238; omega
              · apply DusartPrimeRowsChain.cons
                · change 12239 ≤ 12239; omega
                · change 12239 ≤ 12240; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
