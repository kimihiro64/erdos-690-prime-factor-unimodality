import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 61 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part02_chain :
    DusartPrimeRowsChain 7039 7127 dusartPrimeRows_6977_7332_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 7039 ≤ 7039; omega
  · change 7039 ≤ 7042; omega
  · apply DusartPrimeRowsChain.cons
    · change 7043 ≤ 7043; omega
    · change 7043 ≤ 7056; omega
    · apply DusartPrimeRowsChain.cons
      · change 7057 ≤ 7057; omega
      · change 7057 ≤ 7068; omega
      · apply DusartPrimeRowsChain.cons
        · change 7069 ≤ 7069; omega
        · change 7069 ≤ 7078; omega
        · apply DusartPrimeRowsChain.cons
          · change 7079 ≤ 7079; omega
          · change 7079 ≤ 7102; omega
          · apply DusartPrimeRowsChain.cons
            · change 7103 ≤ 7103; omega
            · change 7103 ≤ 7108; omega
            · apply DusartPrimeRowsChain.cons
              · change 7109 ≤ 7109; omega
              · change 7109 ≤ 7120; omega
              · apply DusartPrimeRowsChain.cons
                · change 7121 ≤ 7121; omega
                · change 7121 ≤ 7126; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
