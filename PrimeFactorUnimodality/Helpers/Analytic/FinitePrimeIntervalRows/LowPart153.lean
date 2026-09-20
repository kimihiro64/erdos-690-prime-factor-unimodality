import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 153 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part02_chain :
    DusartPrimeRowsChain 13451 13523 dusartPrimeRows_13367_14050_part02 := by
  apply DusartPrimeRowsChain.cons
  · change 13451 ≤ 13451; omega
  · change 13451 ≤ 13456; omega
  · apply DusartPrimeRowsChain.cons
    · change 13457 ≤ 13457; omega
    · change 13457 ≤ 13462; omega
    · apply DusartPrimeRowsChain.cons
      · change 13463 ≤ 13463; omega
      · change 13463 ≤ 13468; omega
      · apply DusartPrimeRowsChain.cons
        · change 13469 ≤ 13469; omega
        · change 13469 ≤ 13476; omega
        · apply DusartPrimeRowsChain.cons
          · change 13477 ≤ 13477; omega
          · change 13477 ≤ 13486; omega
          · apply DusartPrimeRowsChain.cons
            · change 13487 ≤ 13487; omega
            · change 13487 ≤ 13498; omega
            · apply DusartPrimeRowsChain.cons
              · change 13499 ≤ 13499; omega
              · change 13499 ≤ 13512; omega
              · apply DusartPrimeRowsChain.cons
                · change 13513 ≤ 13513; omega
                · change 13513 ≤ 13522; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
