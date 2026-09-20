import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 196 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part04_chain :
    DusartPrimeRowsChain 16561 16649 dusartPrimeRows_16319_17158_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 16561 ≤ 16561; omega
  · change 16561 ≤ 16566; omega
  · apply DusartPrimeRowsChain.cons
    · change 16567 ≤ 16567; omega
    · change 16567 ≤ 16572; omega
    · apply DusartPrimeRowsChain.cons
      · change 16573 ≤ 16573; omega
      · change 16573 ≤ 16602; omega
      · apply DusartPrimeRowsChain.cons
        · change 16603 ≤ 16603; omega
        · change 16603 ≤ 16606; omega
        · apply DusartPrimeRowsChain.cons
          · change 16607 ≤ 16607; omega
          · change 16607 ≤ 16618; omega
          · apply DusartPrimeRowsChain.cons
            · change 16619 ≤ 16619; omega
            · change 16619 ≤ 16630; omega
            · apply DusartPrimeRowsChain.cons
              · change 16631 ≤ 16631; omega
              · change 16631 ≤ 16632; omega
              · apply DusartPrimeRowsChain.cons
                · change 16633 ≤ 16633; omega
                · change 16633 ≤ 16648; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
