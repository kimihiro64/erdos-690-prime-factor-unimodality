import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 276 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17519) (q := 17539) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17539) (q := 17551) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17551) (q := 17569) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17569) (q := 17573) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17573) (q := 17579) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17579) (q := 17581) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17581) (q := 17597) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17597) (q := 17599) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part06_chain :
    DusartPrimeRowsChain 17519 17599 dusartPrimeRows_17159_18040_part06 := by
  apply DusartPrimeRowsChain.cons
  · change 17519 ≤ 17519; omega
  · change 17519 ≤ 17538; omega
  · apply DusartPrimeRowsChain.cons
    · change 17539 ≤ 17539; omega
    · change 17539 ≤ 17550; omega
    · apply DusartPrimeRowsChain.cons
      · change 17551 ≤ 17551; omega
      · change 17551 ≤ 17568; omega
      · apply DusartPrimeRowsChain.cons
        · change 17569 ≤ 17569; omega
        · change 17569 ≤ 17572; omega
        · apply DusartPrimeRowsChain.cons
          · change 17573 ≤ 17573; omega
          · change 17573 ≤ 17578; omega
          · apply DusartPrimeRowsChain.cons
            · change 17579 ≤ 17579; omega
            · change 17579 ≤ 17580; omega
            · apply DusartPrimeRowsChain.cons
              · change 17581 ≤ 17581; omega
              · change 17581 ≤ 17596; omega
              · apply DusartPrimeRowsChain.cons
                · change 17597 ≤ 17597; omega
                · change 17597 ≤ 17598; omega
                · apply DusartPrimeRowsChain.empty
                  norm_num
