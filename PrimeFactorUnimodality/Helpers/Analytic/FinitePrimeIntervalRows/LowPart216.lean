import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 216 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part13_chain :
    DusartPrimeRowsChain 22973 23039 dusartPrimeRows_22027_23158_part13 := by
  apply DusartPrimeRowsChain.cons
  · change 22973 ≤ 22973; omega
  · change 22973 ≤ 22992; omega
  · apply DusartPrimeRowsChain.cons
    · change 22993 ≤ 22993; omega
    · change 22993 ≤ 23002; omega
    · apply DusartPrimeRowsChain.cons
      · change 23003 ≤ 23003; omega
      · change 23003 ≤ 23010; omega
      · apply DusartPrimeRowsChain.cons
        · change 23011 ≤ 23011; omega
        · change 23011 ≤ 23016; omega
        · apply DusartPrimeRowsChain.cons
          · change 23017 ≤ 23017; omega
          · change 23017 ≤ 23020; omega
          · apply DusartPrimeRowsChain.cons
            · change 23021 ≤ 23021; omega
            · change 23021 ≤ 23026; omega
            · apply DusartPrimeRowsChain.cons
              · change 23027 ≤ 23027; omega
              · change 23027 ≤ 23028; omega
              · apply DusartPrimeRowsChain.cons
                · change 23029 ≤ 23029; omega
                · change 23029 ≤ 23038; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
