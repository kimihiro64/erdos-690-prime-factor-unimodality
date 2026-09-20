import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 114 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part04_chain :
    DusartPrimeRowsChain 10651 10723 dusartPrimeRows_10427_10938_part04 := by
  apply DusartPrimeRowsChain.cons
  · change 10651 ≤ 10651; omega
  · change 10651 ≤ 10656; omega
  · apply DusartPrimeRowsChain.cons
    · change 10657 ≤ 10657; omega
    · change 10657 ≤ 10662; omega
    · apply DusartPrimeRowsChain.cons
      · change 10663 ≤ 10663; omega
      · change 10663 ≤ 10666; omega
      · apply DusartPrimeRowsChain.cons
        · change 10667 ≤ 10667; omega
        · change 10667 ≤ 10686; omega
        · apply DusartPrimeRowsChain.cons
          · change 10687 ≤ 10687; omega
          · change 10687 ≤ 10690; omega
          · apply DusartPrimeRowsChain.cons
            · change 10691 ≤ 10691; omega
            · change 10691 ≤ 10708; omega
            · apply DusartPrimeRowsChain.cons
              · change 10709 ≤ 10709; omega
              · change 10709 ≤ 10710; omega
              · apply DusartPrimeRowsChain.cons
                · change 10711 ≤ 10711; omega
                · change 10711 ≤ 10722; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
