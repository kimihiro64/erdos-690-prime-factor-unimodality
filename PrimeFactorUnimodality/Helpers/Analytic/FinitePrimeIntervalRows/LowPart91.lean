import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 91 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part02_chain :
    DusartPrimeRowsChain 9029 9109 dusartPrimeRows_8963_9418_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 9029 ≤ 9029; omega
  · change 9029 ≤ 9040; omega
  · apply DusartPrimeRowsChain.cons
    · change 9041 ≤ 9041; omega
    · change 9041 ≤ 9042; omega
    · apply DusartPrimeRowsChain.cons
      · change 9043 ≤ 9043; omega
      · change 9043 ≤ 9048; omega
      · apply DusartPrimeRowsChain.cons
        · change 9049 ≤ 9049; omega
        · change 9049 ≤ 9058; omega
        · apply DusartPrimeRowsChain.cons
          · change 9059 ≤ 9059; omega
          · change 9059 ≤ 9066; omega
          · apply DusartPrimeRowsChain.cons
            · change 9067 ≤ 9067; omega
            · change 9067 ≤ 9090; omega
            · apply DusartPrimeRowsChain.cons
              · change 9091 ≤ 9091; omega
              · change 9091 ≤ 9102; omega
              · apply DusartPrimeRowsChain.cons
                · change 9103 ≤ 9103; omega
                · change 9103 ≤ 9108; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
