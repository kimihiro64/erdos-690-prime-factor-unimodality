import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 95 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part06_chain :
    DusartPrimeRowsChain 9323 9397 dusartPrimeRows_8963_9418_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 9323 ≤ 9323; omega
  · change 9323 ≤ 9336; omega
  · apply DusartPrimeRowsChain.cons
    · change 9337 ≤ 9337; omega
    · change 9337 ≤ 9340; omega
    · apply DusartPrimeRowsChain.cons
      · change 9341 ≤ 9341; omega
      · change 9341 ≤ 9342; omega
      · apply DusartPrimeRowsChain.cons
        · change 9343 ≤ 9343; omega
        · change 9343 ≤ 9348; omega
        · apply DusartPrimeRowsChain.cons
          · change 9349 ≤ 9349; omega
          · change 9349 ≤ 9370; omega
          · apply DusartPrimeRowsChain.cons
            · change 9371 ≤ 9371; omega
            · change 9371 ≤ 9376; omega
            · apply DusartPrimeRowsChain.cons
              · change 9377 ≤ 9377; omega
              · change 9377 ≤ 9390; omega
              · apply DusartPrimeRowsChain.cons
                · change 9391 ≤ 9391; omega
                · change 9391 ≤ 9396; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
