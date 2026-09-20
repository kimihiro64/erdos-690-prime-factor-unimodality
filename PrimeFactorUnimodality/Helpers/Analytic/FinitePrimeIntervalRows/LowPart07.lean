import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part07_chain :
    DusartPrimeRowsChain 3643 3709 dusartPrimeRows_3275_3802_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 3643 ≤ 3643; omega
  · change 3643 ≤ 3658; omega
  · apply DusartPrimeRowsChain.cons
    · change 3659 ≤ 3659; omega
    · change 3659 ≤ 3670; omega
    · apply DusartPrimeRowsChain.cons
      · change 3671 ≤ 3671; omega
      · change 3671 ≤ 3672; omega
      · apply DusartPrimeRowsChain.cons
        · change 3673 ≤ 3673; omega
        · change 3673 ≤ 3676; omega
        · apply DusartPrimeRowsChain.cons
          · change 3677 ≤ 3677; omega
          · change 3677 ≤ 3690; omega
          · apply DusartPrimeRowsChain.cons
            · change 3691 ≤ 3691; omega
            · change 3691 ≤ 3696; omega
            · apply DusartPrimeRowsChain.cons
              · change 3697 ≤ 3697; omega
              · change 3697 ≤ 3700; omega
              · apply DusartPrimeRowsChain.cons
                · change 3701 ≤ 3701; omega
                · change 3701 ≤ 3708; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
