import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 160 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part09_chain :
    DusartPrimeRowsChain 13967 14051 dusartPrimeRows_13367_14050_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 13967 ≤ 13967; omega
  · change 13967 ≤ 13996; omega
  · apply DusartPrimeRowsChain.cons
    · change 13997 ≤ 13997; omega
    · change 13997 ≤ 13998; omega
    · apply DusartPrimeRowsChain.cons
      · change 13999 ≤ 13999; omega
      · change 13999 ≤ 14008; omega
      · apply DusartPrimeRowsChain.cons
        · change 14009 ≤ 14009; omega
        · change 14009 ≤ 14010; omega
        · apply DusartPrimeRowsChain.cons
          · change 14011 ≤ 14011; omega
          · change 14011 ≤ 14028; omega
          · apply DusartPrimeRowsChain.cons
            · change 14029 ≤ 14029; omega
            · change 14029 ≤ 14032; omega
            · apply DusartPrimeRowsChain.cons
              · change 14033 ≤ 14033; omega
              · change 14033 ≤ 14050; omega
              · apply DusartPrimeRowsChain.empty
                norm_num
