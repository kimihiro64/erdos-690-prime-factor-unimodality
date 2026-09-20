import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 266 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18523) (q := 18539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18539) (q := 18541) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18541) (q := 18553) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18553) (q := 18583) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18583) (q := 18587) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18587) (q := 18593) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18593) (q := 18617) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18617) (q := 18637) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part08_chain :
    DusartPrimeRowsChain 18523 18637 dusartPrimeRows_18041_18958_part08 := by
  apply DusartPrimeRowsChain.cons
  · change 18523 ≤ 18523; omega
  · change 18523 ≤ 18538; omega
  · apply DusartPrimeRowsChain.cons
    · change 18539 ≤ 18539; omega
    · change 18539 ≤ 18540; omega
    · apply DusartPrimeRowsChain.cons
      · change 18541 ≤ 18541; omega
      · change 18541 ≤ 18552; omega
      · apply DusartPrimeRowsChain.cons
        · change 18553 ≤ 18553; omega
        · change 18553 ≤ 18582; omega
        · apply DusartPrimeRowsChain.cons
          · change 18583 ≤ 18583; omega
          · change 18583 ≤ 18586; omega
          · apply DusartPrimeRowsChain.cons
            · change 18587 ≤ 18587; omega
            · change 18587 ≤ 18592; omega
            · apply DusartPrimeRowsChain.cons
              · change 18593 ≤ 18593; omega
              · change 18593 ≤ 18616; omega
              · apply DusartPrimeRowsChain.cons
                · change 18617 ≤ 18617; omega
                · change 18617 ≤ 18636; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
