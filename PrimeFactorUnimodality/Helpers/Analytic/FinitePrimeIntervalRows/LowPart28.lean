import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 28 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part02_chain :
    DusartPrimeRowsChain 4969 5021 dusartPrimeRows_4919_5166_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 4969 ≤ 4969; omega
  · change 4969 ≤ 4972; omega
  · apply DusartPrimeRowsChain.cons
    · change 4973 ≤ 4973; omega
    · change 4973 ≤ 4986; omega
    · apply DusartPrimeRowsChain.cons
      · change 4987 ≤ 4987; omega
      · change 4987 ≤ 4992; omega
      · apply DusartPrimeRowsChain.cons
        · change 4993 ≤ 4993; omega
        · change 4993 ≤ 4998; omega
        · apply DusartPrimeRowsChain.cons
          · change 4999 ≤ 4999; omega
          · change 4999 ≤ 5002; omega
          · apply DusartPrimeRowsChain.cons
            · change 5003 ≤ 5003; omega
            · change 5003 ≤ 5008; omega
            · apply DusartPrimeRowsChain.cons
              · change 5009 ≤ 5009; omega
              · change 5009 ≤ 5010; omega
              · apply DusartPrimeRowsChain.cons
                · change 5011 ≤ 5011; omega
                · change 5011 ≤ 5020; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
