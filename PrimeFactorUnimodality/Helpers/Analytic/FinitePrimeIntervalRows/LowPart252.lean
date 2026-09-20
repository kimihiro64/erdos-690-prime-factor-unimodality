import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 252 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19441) (q := 19447) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19447) (q := 19457) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19457) (q := 19463) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19463) (q := 19469) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19469) (q := 19471) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19471) (q := 19477) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19477) (q := 19483) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19483) (q := 19489) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part07_chain :
    DusartPrimeRowsChain 19441 19489 dusartPrimeRows_18959_19936_part07 := by
  apply DusartPrimeRowsChain.cons
  · change 19441 ≤ 19441; omega
  · change 19441 ≤ 19446; omega
  · apply DusartPrimeRowsChain.cons
    · change 19447 ≤ 19447; omega
    · change 19447 ≤ 19456; omega
    · apply DusartPrimeRowsChain.cons
      · change 19457 ≤ 19457; omega
      · change 19457 ≤ 19462; omega
      · apply DusartPrimeRowsChain.cons
        · change 19463 ≤ 19463; omega
        · change 19463 ≤ 19468; omega
        · apply DusartPrimeRowsChain.cons
          · change 19469 ≤ 19469; omega
          · change 19469 ≤ 19470; omega
          · apply DusartPrimeRowsChain.cons
            · change 19471 ≤ 19471; omega
            · change 19471 ≤ 19476; omega
            · apply DusartPrimeRowsChain.cons
              · change 19477 ≤ 19477; omega
              · change 19477 ≤ 19482; omega
              · apply DusartPrimeRowsChain.cons
                · change 19483 ≤ 19483; omega
                · change 19483 ≤ 19488; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
