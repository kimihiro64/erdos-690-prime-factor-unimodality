import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 272 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17231) (q := 17239) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17239) (q := 17257) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17257) (q := 17291) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17291) (q := 17293) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17293) (q := 17299) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17299) (q := 17317) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17317) (q := 17321) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17321) (q := 17327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part02_chain :
    DusartPrimeRowsChain 17231 17327 dusartPrimeRows_17159_18040_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 17231 ≤ 17231; omega
  · change 17231 ≤ 17238; omega
  · apply DusartPrimeRowsChain.cons
    · change 17239 ≤ 17239; omega
    · change 17239 ≤ 17256; omega
    · apply DusartPrimeRowsChain.cons
      · change 17257 ≤ 17257; omega
      · change 17257 ≤ 17290; omega
      · apply DusartPrimeRowsChain.cons
        · change 17291 ≤ 17291; omega
        · change 17291 ≤ 17292; omega
        · apply DusartPrimeRowsChain.cons
          · change 17293 ≤ 17293; omega
          · change 17293 ≤ 17298; omega
          · apply DusartPrimeRowsChain.cons
            · change 17299 ≤ 17299; omega
            · change 17299 ≤ 17316; omega
            · apply DusartPrimeRowsChain.cons
              · change 17317 ≤ 17317; omega
              · change 17317 ≤ 17320; omega
              · apply DusartPrimeRowsChain.cons
                · change 17321 ≤ 17321; omega
                · change 17321 ≤ 17326; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
