import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 86 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part04_chain :
    DusartPrimeRowsChain 8713 8779 dusartPrimeRows_8521_8962_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 8713 ≤ 8713; omega
  · change 8713 ≤ 8718; omega
  · apply DusartPrimeRowsChain.cons
    · change 8719 ≤ 8719; omega
    · change 8719 ≤ 8730; omega
    · apply DusartPrimeRowsChain.cons
      · change 8731 ≤ 8731; omega
      · change 8731 ≤ 8736; omega
      · apply DusartPrimeRowsChain.cons
        · change 8737 ≤ 8737; omega
        · change 8737 ≤ 8740; omega
        · apply DusartPrimeRowsChain.cons
          · change 8741 ≤ 8741; omega
          · change 8741 ≤ 8746; omega
          · apply DusartPrimeRowsChain.cons
            · change 8747 ≤ 8747; omega
            · change 8747 ≤ 8752; omega
            · apply DusartPrimeRowsChain.cons
              · change 8753 ≤ 8753; omega
              · change 8753 ≤ 8760; omega
              · apply DusartPrimeRowsChain.cons
                · change 8761 ≤ 8761; omega
                · change 8761 ≤ 8778; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
