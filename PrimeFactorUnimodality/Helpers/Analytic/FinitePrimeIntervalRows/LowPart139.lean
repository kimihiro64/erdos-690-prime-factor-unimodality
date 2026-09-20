import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 139 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12517 dusartPrimeRows_12097_12712_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 12457 ≤ 12457; omega
  · change 12457 ≤ 12472; omega
  · apply DusartPrimeRowsChain.cons
    · change 12473 ≤ 12473; omega
    · change 12473 ≤ 12478; omega
    · apply DusartPrimeRowsChain.cons
      · change 12479 ≤ 12479; omega
      · change 12479 ≤ 12486; omega
      · apply DusartPrimeRowsChain.cons
        · change 12487 ≤ 12487; omega
        · change 12487 ≤ 12490; omega
        · apply DusartPrimeRowsChain.cons
          · change 12491 ≤ 12491; omega
          · change 12491 ≤ 12496; omega
          · apply DusartPrimeRowsChain.cons
            · change 12497 ≤ 12497; omega
            · change 12497 ≤ 12502; omega
            · apply DusartPrimeRowsChain.cons
              · change 12503 ≤ 12503; omega
              · change 12503 ≤ 12510; omega
              · apply DusartPrimeRowsChain.cons
                · change 12511 ≤ 12511; omega
                · change 12511 ≤ 12516; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
