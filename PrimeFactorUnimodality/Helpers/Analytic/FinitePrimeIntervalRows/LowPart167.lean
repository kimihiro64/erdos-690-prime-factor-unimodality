import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 167 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part07_chain :
    DusartPrimeRowsChain 14551 14629 dusartPrimeRows_14051_14766_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 14551 ≤ 14551; omega
  · change 14551 ≤ 14556; omega
  · apply DusartPrimeRowsChain.cons
    · change 14557 ≤ 14557; omega
    · change 14557 ≤ 14560; omega
    · apply DusartPrimeRowsChain.cons
      · change 14561 ≤ 14561; omega
      · change 14561 ≤ 14562; omega
      · apply DusartPrimeRowsChain.cons
        · change 14563 ≤ 14563; omega
        · change 14563 ≤ 14590; omega
        · apply DusartPrimeRowsChain.cons
          · change 14591 ≤ 14591; omega
          · change 14591 ≤ 14592; omega
          · apply DusartPrimeRowsChain.cons
            · change 14593 ≤ 14593; omega
            · change 14593 ≤ 14620; omega
            · apply DusartPrimeRowsChain.cons
              · change 14621 ≤ 14621; omega
              · change 14621 ≤ 14626; omega
              · apply DusartPrimeRowsChain.cons
                · change 14627 ≤ 14627; omega
                · change 14627 ≤ 14628; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
