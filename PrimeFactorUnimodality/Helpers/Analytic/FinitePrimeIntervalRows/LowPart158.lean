import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 158 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part07_chain :
    DusartPrimeRowsChain 13829 13901 dusartPrimeRows_13367_14050_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 13829 ≤ 13829; omega
  · change 13829 ≤ 13830; omega
  · apply DusartPrimeRowsChain.cons
    · change 13831 ≤ 13831; omega
    · change 13831 ≤ 13840; omega
    · apply DusartPrimeRowsChain.cons
      · change 13841 ≤ 13841; omega
      · change 13841 ≤ 13858; omega
      · apply DusartPrimeRowsChain.cons
        · change 13859 ≤ 13859; omega
        · change 13859 ≤ 13872; omega
        · apply DusartPrimeRowsChain.cons
          · change 13873 ≤ 13873; omega
          · change 13873 ≤ 13876; omega
          · apply DusartPrimeRowsChain.cons
            · change 13877 ≤ 13877; omega
            · change 13877 ≤ 13878; omega
            · apply DusartPrimeRowsChain.cons
              · change 13879 ≤ 13879; omega
              · change 13879 ≤ 13882; omega
              · apply DusartPrimeRowsChain.cons
                · change 13883 ≤ 13883; omega
                · change 13883 ≤ 13900; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
