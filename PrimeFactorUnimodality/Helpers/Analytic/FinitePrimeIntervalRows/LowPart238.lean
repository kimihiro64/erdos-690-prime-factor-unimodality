import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 238 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20323) (q := 20327) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20327) (q := 20333) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20333) (q := 20341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20341) (q := 20347) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20347) (q := 20353) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20353) (q := 20357) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20357) (q := 20359) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20359) (q := 20369) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part06_chain :
    DusartPrimeRowsChain 20323 20369 dusartPrimeRows_19937_20958_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 20323 ≤ 20323; omega
  · change 20323 ≤ 20326; omega
  · apply DusartPrimeRowsChain.cons
    · change 20327 ≤ 20327; omega
    · change 20327 ≤ 20332; omega
    · apply DusartPrimeRowsChain.cons
      · change 20333 ≤ 20333; omega
      · change 20333 ≤ 20340; omega
      · apply DusartPrimeRowsChain.cons
        · change 20341 ≤ 20341; omega
        · change 20341 ≤ 20346; omega
        · apply DusartPrimeRowsChain.cons
          · change 20347 ≤ 20347; omega
          · change 20347 ≤ 20352; omega
          · apply DusartPrimeRowsChain.cons
            · change 20353 ≤ 20353; omega
            · change 20353 ≤ 20356; omega
            · apply DusartPrimeRowsChain.cons
              · change 20357 ≤ 20357; omega
              · change 20357 ≤ 20358; omega
              · apply DusartPrimeRowsChain.cons
                · change 20359 ≤ 20359; omega
                · change 20359 ≤ 20368; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
