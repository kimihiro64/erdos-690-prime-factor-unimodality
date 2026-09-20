import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 268 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18731) (q := 18743) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18743) (q := 18749) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18749) (q := 18757) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18757) (q := 18773) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18773) (q := 18787) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18787) (q := 18793) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18793) (q := 18797) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18797) (q := 18803) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part10_chain :
    DusartPrimeRowsChain 18731 18803 dusartPrimeRows_18041_18958_part10 := by
  apply DusartPrimeRowsChain.cons
  · change 18731 ≤ 18731; omega
  · change 18731 ≤ 18742; omega
  · apply DusartPrimeRowsChain.cons
    · change 18743 ≤ 18743; omega
    · change 18743 ≤ 18748; omega
    · apply DusartPrimeRowsChain.cons
      · change 18749 ≤ 18749; omega
      · change 18749 ≤ 18756; omega
      · apply DusartPrimeRowsChain.cons
        · change 18757 ≤ 18757; omega
        · change 18757 ≤ 18772; omega
        · apply DusartPrimeRowsChain.cons
          · change 18773 ≤ 18773; omega
          · change 18773 ≤ 18786; omega
          · apply DusartPrimeRowsChain.cons
            · change 18787 ≤ 18787; omega
            · change 18787 ≤ 18792; omega
            · apply DusartPrimeRowsChain.cons
              · change 18793 ≤ 18793; omega
              · change 18793 ≤ 18796; omega
              · apply DusartPrimeRowsChain.cons
                · change 18797 ≤ 18797; omega
                · change 18797 ≤ 18802; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
