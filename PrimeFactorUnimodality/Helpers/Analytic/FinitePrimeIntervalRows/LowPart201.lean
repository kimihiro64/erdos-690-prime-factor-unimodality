import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 201 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part09_chain :
    DusartPrimeRowsChain 16979 17033 dusartPrimeRows_16319_17158_part09 := by
  apply DusartPrimeRowsChain.cons
  · change 16979 ≤ 16979; omega
  · change 16979 ≤ 16980; omega
  · apply DusartPrimeRowsChain.cons
    · change 16981 ≤ 16981; omega
    · change 16981 ≤ 16986; omega
    · apply DusartPrimeRowsChain.cons
      · change 16987 ≤ 16987; omega
      · change 16987 ≤ 16992; omega
      · apply DusartPrimeRowsChain.cons
        · change 16993 ≤ 16993; omega
        · change 16993 ≤ 17010; omega
        · apply DusartPrimeRowsChain.cons
          · change 17011 ≤ 17011; omega
          · change 17011 ≤ 17020; omega
          · apply DusartPrimeRowsChain.cons
            · change 17021 ≤ 17021; omega
            · change 17021 ≤ 17026; omega
            · apply DusartPrimeRowsChain.cons
              · change 17027 ≤ 17027; omega
              · change 17027 ≤ 17028; omega
              · apply DusartPrimeRowsChain.cons
                · change 17029 ≤ 17029; omega
                · change 17029 ≤ 17032; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
