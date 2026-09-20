import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 244 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20789) (q := 20807) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20807) (q := 20809) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20809) (q := 20849) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20849) (q := 20857) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20857) (q := 20873) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20873) (q := 20879) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20879) (q := 20887) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20887) (q := 20897) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part12_chain :
    DusartPrimeRowsChain 20789 20897 dusartPrimeRows_19937_20958_part12 := by
  apply DusartPrimeRowsChain.cons
  · change 20789 ≤ 20789; omega
  · change 20789 ≤ 20806; omega
  · apply DusartPrimeRowsChain.cons
    · change 20807 ≤ 20807; omega
    · change 20807 ≤ 20808; omega
    · apply DusartPrimeRowsChain.cons
      · change 20809 ≤ 20809; omega
      · change 20809 ≤ 20848; omega
      · apply DusartPrimeRowsChain.cons
        · change 20849 ≤ 20849; omega
        · change 20849 ≤ 20856; omega
        · apply DusartPrimeRowsChain.cons
          · change 20857 ≤ 20857; omega
          · change 20857 ≤ 20872; omega
          · apply DusartPrimeRowsChain.cons
            · change 20873 ≤ 20873; omega
            · change 20873 ≤ 20878; omega
            · apply DusartPrimeRowsChain.cons
              · change 20879 ≤ 20879; omega
              · change 20879 ≤ 20886; omega
              · apply DusartPrimeRowsChain.cons
                · change 20887 ≤ 20887; omega
                · change 20887 ≤ 20896; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
