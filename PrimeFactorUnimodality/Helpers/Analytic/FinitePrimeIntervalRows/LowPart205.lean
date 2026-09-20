import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 205 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part02_chain :
    DusartPrimeRowsChain 22079 22147 dusartPrimeRows_22027_23158_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 22079 ≤ 22079; omega
  · change 22079 ≤ 22090; omega
  · apply DusartPrimeRowsChain.cons
    · change 22091 ≤ 22091; omega
    · change 22091 ≤ 22092; omega
    · apply DusartPrimeRowsChain.cons
      · change 22093 ≤ 22093; omega
      · change 22093 ≤ 22108; omega
      · apply DusartPrimeRowsChain.cons
        · change 22109 ≤ 22109; omega
        · change 22109 ≤ 22110; omega
        · apply DusartPrimeRowsChain.cons
          · change 22111 ≤ 22111; omega
          · change 22111 ≤ 22122; omega
          · apply DusartPrimeRowsChain.cons
            · change 22123 ≤ 22123; omega
            · change 22123 ≤ 22128; omega
            · apply DusartPrimeRowsChain.cons
              · change 22129 ≤ 22129; omega
              · change 22129 ≤ 22132; omega
              · apply DusartPrimeRowsChain.cons
                · change 22133 ≤ 22133; omega
                · change 22133 ≤ 22146; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
