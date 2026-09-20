import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 68 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part04_chain :
    DusartPrimeRowsChain 7559 7607 dusartPrimeRows_7333_7716_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 7559 ≤ 7559; omega
  · change 7559 ≤ 7560; omega
  · apply DusartPrimeRowsChain.cons
    · change 7561 ≤ 7561; omega
    · change 7561 ≤ 7572; omega
    · apply DusartPrimeRowsChain.cons
      · change 7573 ≤ 7573; omega
      · change 7573 ≤ 7576; omega
      · apply DusartPrimeRowsChain.cons
        · change 7577 ≤ 7577; omega
        · change 7577 ≤ 7582; omega
        · apply DusartPrimeRowsChain.cons
          · change 7583 ≤ 7583; omega
          · change 7583 ≤ 7588; omega
          · apply DusartPrimeRowsChain.cons
            · change 7589 ≤ 7589; omega
            · change 7589 ≤ 7590; omega
            · apply DusartPrimeRowsChain.cons
              · change 7591 ≤ 7591; omega
              · change 7591 ≤ 7602; omega
              · apply DusartPrimeRowsChain.cons
                · change 7603 ≤ 7603; omega
                · change 7603 ≤ 7606; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
