import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 08 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part08_chain :
    DusartPrimeRowsChain 3709 3779 dusartPrimeRows_3275_3802_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 3709 ≤ 3709; omega
  · change 3709 ≤ 3718; omega
  · apply DusartPrimeRowsChain.cons
    · change 3719 ≤ 3719; omega
    · change 3719 ≤ 3726; omega
    · apply DusartPrimeRowsChain.cons
      · change 3727 ≤ 3727; omega
      · change 3727 ≤ 3732; omega
      · apply DusartPrimeRowsChain.cons
        · change 3733 ≤ 3733; omega
        · change 3733 ≤ 3738; omega
        · apply DusartPrimeRowsChain.cons
          · change 3739 ≤ 3739; omega
          · change 3739 ≤ 3760; omega
          · apply DusartPrimeRowsChain.cons
            · change 3761 ≤ 3761; omega
            · change 3761 ≤ 3766; omega
            · apply DusartPrimeRowsChain.cons
              · change 3767 ≤ 3767; omega
              · change 3767 ≤ 3768; omega
              · apply DusartPrimeRowsChain.cons
                · change 3769 ≤ 3769; omega
                · change 3769 ≤ 3778; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
