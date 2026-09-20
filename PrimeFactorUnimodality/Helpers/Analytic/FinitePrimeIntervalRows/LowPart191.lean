import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 191 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part10_chain :
    DusartPrimeRowsChain 16217 16301 dusartPrimeRows_15527_16318_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 16217 ≤ 16217; omega
  · change 16217 ≤ 16222; omega
  · apply DusartPrimeRowsChain.cons
    · change 16223 ≤ 16223; omega
    · change 16223 ≤ 16228; omega
    · apply DusartPrimeRowsChain.cons
      · change 16229 ≤ 16229; omega
      · change 16229 ≤ 16230; omega
      · apply DusartPrimeRowsChain.cons
        · change 16231 ≤ 16231; omega
        · change 16231 ≤ 16248; omega
        · apply DusartPrimeRowsChain.cons
          · change 16249 ≤ 16249; omega
          · change 16249 ≤ 16252; omega
          · apply DusartPrimeRowsChain.cons
            · change 16253 ≤ 16253; omega
            · change 16253 ≤ 16266; omega
            · apply DusartPrimeRowsChain.cons
              · change 16267 ≤ 16267; omega
              · change 16267 ≤ 16272; omega
              · apply DusartPrimeRowsChain.cons
                · change 16273 ≤ 16273; omega
                · change 16273 ≤ 16300; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
