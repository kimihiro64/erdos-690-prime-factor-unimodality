import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 73 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part03_chain :
    DusartPrimeRowsChain 7877 7937 dusartPrimeRows_7717_8110_part03 := by
  apply DusartPrimeRowsChain.cons
  · change 7877 ≤ 7877; omega
  · change 7877 ≤ 7878; omega
  · apply DusartPrimeRowsChain.cons
    · change 7879 ≤ 7879; omega
    · change 7879 ≤ 7882; omega
    · apply DusartPrimeRowsChain.cons
      · change 7883 ≤ 7883; omega
      · change 7883 ≤ 7900; omega
      · apply DusartPrimeRowsChain.cons
        · change 7901 ≤ 7901; omega
        · change 7901 ≤ 7906; omega
        · apply DusartPrimeRowsChain.cons
          · change 7907 ≤ 7907; omega
          · change 7907 ≤ 7918; omega
          · apply DusartPrimeRowsChain.cons
            · change 7919 ≤ 7919; omega
            · change 7919 ≤ 7926; omega
            · apply DusartPrimeRowsChain.cons
              · change 7927 ≤ 7927; omega
              · change 7927 ≤ 7932; omega
              · apply DusartPrimeRowsChain.cons
                · change 7933 ≤ 7933; omega
                · change 7933 ≤ 7936; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
