import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 90 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part01_chain :
    DusartPrimeRowsChain 8963 9029 dusartPrimeRows_8963_9418_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 8963 ≤ 8963; omega
  · change 8963 ≤ 8968; omega
  · apply DusartPrimeRowsChain.cons
    · change 8969 ≤ 8969; omega
    · change 8969 ≤ 8970; omega
    · apply DusartPrimeRowsChain.cons
      · change 8971 ≤ 8971; omega
      · change 8971 ≤ 8998; omega
      · apply DusartPrimeRowsChain.cons
        · change 8999 ≤ 8999; omega
        · change 8999 ≤ 9000; omega
        · apply DusartPrimeRowsChain.cons
          · change 9001 ≤ 9001; omega
          · change 9001 ≤ 9006; omega
          · apply DusartPrimeRowsChain.cons
            · change 9007 ≤ 9007; omega
            · change 9007 ≤ 9010; omega
            · apply DusartPrimeRowsChain.cons
              · change 9011 ≤ 9011; omega
              · change 9011 ≤ 9012; omega
              · apply DusartPrimeRowsChain.cons
                · change 9013 ≤ 9013; omega
                · change 9013 ≤ 9028; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
