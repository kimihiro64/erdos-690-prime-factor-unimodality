import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 204 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part01_chain :
    DusartPrimeRowsChain 22027 22079 dusartPrimeRows_22027_23158_part01 := by
  apply DusartPrimeRowsChain.cons
  · change 22027 ≤ 22027; omega
  · change 22027 ≤ 22030; omega
  · apply DusartPrimeRowsChain.cons
    · change 22031 ≤ 22031; omega
    · change 22031 ≤ 22036; omega
    · apply DusartPrimeRowsChain.cons
      · change 22037 ≤ 22037; omega
      · change 22037 ≤ 22038; omega
      · apply DusartPrimeRowsChain.cons
        · change 22039 ≤ 22039; omega
        · change 22039 ≤ 22050; omega
        · apply DusartPrimeRowsChain.cons
          · change 22051 ≤ 22051; omega
          · change 22051 ≤ 22062; omega
          · apply DusartPrimeRowsChain.cons
            · change 22063 ≤ 22063; omega
            · change 22063 ≤ 22066; omega
            · apply DusartPrimeRowsChain.cons
              · change 22067 ≤ 22067; omega
              · change 22067 ≤ 22072; omega
              · apply DusartPrimeRowsChain.cons
                · change 22073 ≤ 22073; omega
                · change 22073 ≤ 22078; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
