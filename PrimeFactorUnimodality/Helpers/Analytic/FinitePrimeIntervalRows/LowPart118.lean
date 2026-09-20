import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 118 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part01_chain :
    DusartPrimeRowsChain 10939 11027 dusartPrimeRows_10939_11502_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 10939 ≤ 10939; omega
  · change 10939 ≤ 10948; omega
  · apply DusartPrimeRowsChain.cons
    · change 10949 ≤ 10949; omega
    · change 10949 ≤ 10956; omega
    · apply DusartPrimeRowsChain.cons
      · change 10957 ≤ 10957; omega
      · change 10957 ≤ 10972; omega
      · apply DusartPrimeRowsChain.cons
        · change 10973 ≤ 10973; omega
        · change 10973 ≤ 10978; omega
        · apply DusartPrimeRowsChain.cons
          · change 10979 ≤ 10979; omega
          · change 10979 ≤ 10986; omega
          · apply DusartPrimeRowsChain.cons
            · change 10987 ≤ 10987; omega
            · change 10987 ≤ 10992; omega
            · apply DusartPrimeRowsChain.cons
              · change 10993 ≤ 10993; omega
              · change 10993 ≤ 11002; omega
              · apply DusartPrimeRowsChain.cons
                · change 11003 ≤ 11003; omega
                · change 11003 ≤ 11026; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
