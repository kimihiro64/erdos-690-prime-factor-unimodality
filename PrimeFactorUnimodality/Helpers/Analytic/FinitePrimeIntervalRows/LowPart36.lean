import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 36 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part02_chain :
    DusartPrimeRowsChain 5501 5563 dusartPrimeRows_5437_5710_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 5501 ≤ 5501; omega
  · change 5501 ≤ 5502; omega
  · apply DusartPrimeRowsChain.cons
    · change 5503 ≤ 5503; omega
    · change 5503 ≤ 5506; omega
    · apply DusartPrimeRowsChain.cons
      · change 5507 ≤ 5507; omega
      · change 5507 ≤ 5518; omega
      · apply DusartPrimeRowsChain.cons
        · change 5519 ≤ 5519; omega
        · change 5519 ≤ 5520; omega
        · apply DusartPrimeRowsChain.cons
          · change 5521 ≤ 5521; omega
          · change 5521 ≤ 5526; omega
          · apply DusartPrimeRowsChain.cons
            · change 5527 ≤ 5527; omega
            · change 5527 ≤ 5530; omega
            · apply DusartPrimeRowsChain.cons
              · change 5531 ≤ 5531; omega
              · change 5531 ≤ 5556; omega
              · apply DusartPrimeRowsChain.cons
                · change 5557 ≤ 5557; omega
                · change 5557 ≤ 5562; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
