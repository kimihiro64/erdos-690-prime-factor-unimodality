import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 186 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part05_chain :
    DusartPrimeRowsChain 15803 15889 dusartPrimeRows_15527_16318_part05 := by
  apply DusartPrimeRowsChain.cons
  · change 15803 ≤ 15803; omega
  · change 15803 ≤ 15808; omega
  · apply DusartPrimeRowsChain.cons
    · change 15809 ≤ 15809; omega
    · change 15809 ≤ 15816; omega
    · apply DusartPrimeRowsChain.cons
      · change 15817 ≤ 15817; omega
      · change 15817 ≤ 15822; omega
      · apply DusartPrimeRowsChain.cons
        · change 15823 ≤ 15823; omega
        · change 15823 ≤ 15858; omega
        · apply DusartPrimeRowsChain.cons
          · change 15859 ≤ 15859; omega
          · change 15859 ≤ 15876; omega
          · apply DusartPrimeRowsChain.cons
            · change 15877 ≤ 15877; omega
            · change 15877 ≤ 15880; omega
            · apply DusartPrimeRowsChain.cons
              · change 15881 ≤ 15881; omega
              · change 15881 ≤ 15886; omega
              · apply DusartPrimeRowsChain.cons
                · change 15887 ≤ 15887; omega
                · change 15887 ≤ 15888; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
