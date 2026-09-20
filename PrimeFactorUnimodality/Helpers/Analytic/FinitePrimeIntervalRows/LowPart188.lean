import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 188 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part07_chain :
    DusartPrimeRowsChain 15971 16063 dusartPrimeRows_15527_16318_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 15971 ≤ 15971; omega
  · change 15971 ≤ 15972; omega
  · apply DusartPrimeRowsChain.cons
    · change 15973 ≤ 15973; omega
    · change 15973 ≤ 15990; omega
    · apply DusartPrimeRowsChain.cons
      · change 15991 ≤ 15991; omega
      · change 15991 ≤ 16000; omega
      · apply DusartPrimeRowsChain.cons
        · change 16001 ≤ 16001; omega
        · change 16001 ≤ 16006; omega
        · apply DusartPrimeRowsChain.cons
          · change 16007 ≤ 16007; omega
          · change 16007 ≤ 16032; omega
          · apply DusartPrimeRowsChain.cons
            · change 16033 ≤ 16033; omega
            · change 16033 ≤ 16056; omega
            · apply DusartPrimeRowsChain.cons
              · change 16057 ≤ 16057; omega
              · change 16057 ≤ 16060; omega
              · apply DusartPrimeRowsChain.cons
                · change 16061 ≤ 16061; omega
                · change 16061 ≤ 16062; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
