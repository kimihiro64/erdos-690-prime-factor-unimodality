import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 197 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part05_chain :
    DusartPrimeRowsChain 16649 16703 dusartPrimeRows_16319_17158_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 16649 ≤ 16649; omega
  · change 16649 ≤ 16650; omega
  · apply DusartPrimeRowsChain.cons
    · change 16651 ≤ 16651; omega
    · change 16651 ≤ 16656; omega
    · apply DusartPrimeRowsChain.cons
      · change 16657 ≤ 16657; omega
      · change 16657 ≤ 16660; omega
      · apply DusartPrimeRowsChain.cons
        · change 16661 ≤ 16661; omega
        · change 16661 ≤ 16672; omega
        · apply DusartPrimeRowsChain.cons
          · change 16673 ≤ 16673; omega
          · change 16673 ≤ 16690; omega
          · apply DusartPrimeRowsChain.cons
            · change 16691 ≤ 16691; omega
            · change 16691 ≤ 16692; omega
            · apply DusartPrimeRowsChain.cons
              · change 16693 ≤ 16693; omega
              · change 16693 ≤ 16698; omega
              · apply DusartPrimeRowsChain.cons
                · change 16699 ≤ 16699; omega
                · change 16699 ≤ 16702; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
